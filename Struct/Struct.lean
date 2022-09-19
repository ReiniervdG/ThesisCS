import Lean

import Struct.Helpers
import Struct.CustomTactics

open 
  Lean 
  Lean.Expr
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

-- TMP for debugging
set_option pp.rawOnError true

/-
  # Description of this file ..

-/

structure StateDiff where
  newlyChangedGoal : Option Term
  newDecls : Array LocalDecl
  changedDecls : Array LocalDecl
  removedDecls : Array LocalDecl

def StateDiff.toMessageData (s : StateDiff) : MessageData :=
  m!"isGoalChanged: {if s.newlyChangedGoal == none then "false" else "true"}, 
      newDecls: [{s.newDecls.map fun ldecl => ldecl.type}], 
      changedDecls: [{s.changedDecls.map fun ldecl => ldecl.type}],
      removedDecls: [ {s.removedDecls.map fun ldecl => ldecl.type} ]"

def goalsToStateDiff (oldGoal : MVarId) (newGoal : MVarId) : TacticM StateDiff := do
  let oldGoalType ← instantiateMVars (← oldGoal.getDecl).type
  let newGoalType ← instantiateMVars (← newGoal.getDecl).type
  let isSameGoal := oldGoalType.consumeMData == newGoalType.consumeMData
  let newlyChangedGoal := if isSameGoal then none else some (← delab newGoalType)

  let oldLCtx := (← oldGoal.getDecl).lctx
  let newLCtx := (← newGoal.getDecl).lctx

  let mut newDecls := #[]
  let mut changedDecls := #[]
  let mut removedDecls := #[]

  for newDecl in newLCtx do
    let mut foundMatch : Bool := false
    for oldDecl in oldLCtx do
      if newDecl.userName == oldDecl.userName then
        foundMatch := true
        if !(newDecl.type.consumeMData == oldDecl.type.consumeMData) then
          changedDecls := changedDecls.push newDecl
    if !foundMatch then
      newDecls := newDecls.push newDecl

  for oldDecl in oldLCtx do
    let mut foundMatch : Bool := false
    for newDecl in newLCtx do
      if oldDecl.userName == newDecl.userName then
        foundMatch := true
    if !foundMatch then
      removedDecls := removedDecls.push oldDecl

  return StateDiff.mk newlyChangedGoal newDecls changedDecls removedDecls

-- ## Helpers ..
def getTacs (ts : TSyntax ``tacticSeq) : TermElabM (Array (TSyntax `tactic)) :=
  match ts with
  | `(tacticSeq| { $[$tacs:tactic $[;]?]* }) => return tacs
  | `(tacticSeq| $[$tacs:tactic $[;]?]*) => return tacs
  | _ => throwError "unknown syntax"

def declToBinder (decl : LocalDecl) : TermElabM (TSyntax `strucBinder) := do
  if decl.userName.hasMacroScopes then
    return (← `(strucBinder|(_ : $(← delab decl.type))))
  else 
    return (← `(strucBinder|($(mkIdent decl.userName) : $(← delab decl.type))))

-- TODO : strip original tacSeq of comments (optional)

-- ## State to tactic(Seq) builders
def mkShow (newGoalTerm : Term) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  `(tactic|show $newGoalTerm by $tacSeq)
 
def mkSuffices (newGoalTerm : Term) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  `(tactic|suffices $newGoalTerm by $tacSeq)

def mkHave (decl : LocalDecl) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  let declType ← delab (← instantiateMVars decl.type)
  match decl.userName.hasMacroScopes with
  | true => 
    let id := mkIdent decl.userName
    `(tactic|have $id : $declType := by $tacSeq)
  | false => 
    `(tactic|have : $declType := by $tacSeq)

def mkFix (decls : Array LocalDecl) (goal : Term) : TermElabM (TSyntax `tactic) := do
  let binders ← decls.mapM (fun decl => declToBinder decl)
  `(tactic|fix $[$binders]* ⊢ $goal)

def mkNote (decls : Array LocalDecl := #[]) (optGoal : Option Term := none) (optTacSeq : Option (TSyntax ``tacticSeq)) : TermElabM (TSyntax `tactic) := do
  let binders ← decls.mapM (fun decl => declToBinder decl)  
  match optGoal with
  | some goal => 
    match optTacSeq with
    | some tacSeq => `(tactic|note $[$binders]* ⊢ $goal by $tacSeq)
    | none => `(tactic|note $[$binders]* ⊢ $goal)
  | none => 
    match optTacSeq with
    | some tacSeq => `(tactic|note $[$binders]* by $tacSeq)
    | none => 
      if binders.size == 0 then
        throwError "Nothing to note, TODO"
      else
        `(tactic|note $[$binders]*)

-- def mkCasesMatch
-- def mkInductionMatch
def mkCases (x : TSyntax ``casesTarget) (y : TSyntax ``binderIdent) : TermElabM (TSyntax ``tacticSeq) := do
  `(tacticSeq|
    cases $x
    case $y =>
      rfl)

-- def mkCase
-- def mkDefaultCases

-- ## Structured branches
def structuredIntros (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  evalTactic tacSeq
  match (← getUnsolvedGoals) with
  | [] => throwError "Finishing with intros should be impossible"
  | [newGoal] => 
    let s ← goalsToStateDiff oldGoal newGoal

    match (s.newlyChangedGoal, s.newDecls, s.changedDecls, s.removedDecls) with
    | ((some newGoalTerm), newDecls, changedDecls, #[]) => 
      let suggestion ← mkFix (newDecls ++ changedDecls) newGoalTerm
      addTrace `structured m!"Try this: {suggestion}"
    | _ => throwError "Unexpected state: {StateDiff.toMessageData s}"
  | _ => throwError "Unexpected state: Multiple goals after executing intro statement"

def structuredCases (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (target : TSyntax ``casesTarget) : TacticM Unit := do
  -- Initial investigation: can we retrieve from the target and its specification in the env how to construct a match statement
  -- (or even, how many declarations are constructed by each specific case, kind of num of ldecls with macroScopes)
  let env ← getEnv

  -- TODO: to create a cases tactic, we need all information at once, since we cannot seem to create a single `| _` element separately
  let tmp ← `(tactic|cases n with | _ | succ m => rfl)

  -- For the final cases tactic, we need 
  --   (1) casesTarget, which we already have
  --   (2) A list of lines for each case
  --      * The stripped Name (e.g. `zero` for `Nat.zero`)
  --      * The number of arguments to add, or already a list of automatically generated names for each (prepended with the ctor name)


  match target with
  | `(casesTarget|$targetTerm:term)
  | `(casesTarget|$_ : $targetTerm:term) =>
    -- TODO: I get casesTarget as a term, but from what I've seen, I match the name of the case from the Expr.const
    -- Elaborating this term does not seem to have the desired form
    let targetExpr ← elabTerm targetTerm none
    let targetType ← inferType targetExpr

    -- Get expr of underlying function application
    let fnExpr := getAppFn targetType

    -- Match that Expr with its name in the environment
    match fnExpr with
    | .const fnName _ => 
      let cstInfo := env.find? fnName

      match cstInfo with 
      | some (.inductInfo ival) => 
        let ctors := ival.ctors
        -- for Nat, `ctors := [Nat.zero, Nat.succ]`
        addTrace `xx m!"Constructors: {ctors}"
        
        for ctor in ctors do
          let ctorInfo := env.find? ctor
          match ctor with
          | .str _ s => addTrace `xx m!"TMP: {s}"
          | _ => pure ()
          

          match ctorInfo with
          | some (.ctorInfo cval) =>
            addTrace `xx m!"Constructor {ctor} for inductive type {cval.induct} with numParams {cval.numParams}, numFields {cval.numFields}, with type repr: {repr cval.type}"
          | _ => 
            addTrace `xx m!"Unexpected 04"
        
      | _ => 
        addTrace `xx m!"Unexpected error 03"

    -- TODO: reaching this, elaboratedTerm is currently not a const
    | _ => addTrace `xx m!"Unexpected error 02, targetType: {repr targetType}, fnExpr: {repr fnExpr}"
  | _ => addTrace `xx m!"Unexpected error 01"

-- def structuredInduction
-- Should be pretty similar to structuredCases, except with a different tacSeq match. Could potentially be combined, depending on construction of match statement

-- structuredCasesDefault: When multiple post-goals, but no match on cases or induction
def structureCasesDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (newGoals : List MVarId) : TacticM Unit := do
  let mut cases : Array (TSyntax `tactic) := #[]

  -- Construct a case for each new goal
  -- TODO : Move to separate function and use MapM
  for newGoal in newGoals do
    let goalUserName := (← newGoal.getDecl).userName
    
    -- Compare newGoal to oldGoal
    -- TODO new comparison implementation
    let s ← goalsToStateDiff oldGoal newGoal

    -- Major TODO: detect inaccessible local context, add to case statement

    -- Construct change annotation
    let annotation ← mkNote #[] s.newlyChangedGoal none

    -- Construct full case
    let caseId := mkIdent goalUserName
    let caseIdName := mkIdent (← newGoal.getTag)
    let caseBinderId : TSyntax ``binderIdent ← `(binderIdent|$caseIdName:ident)
    let case ← `(tactic|case $caseBinderId => 
      $annotation:tactic
      sorry) -- TODO: Currently adding sorry to make sure suggestion is actualy syntactically correct
    cases := cases.push case  
  
  -- Append all 
  let suggestion ← mkTacticSeqAppendTacs tacSeq cases
  addTrace `structured m!"Try this: {suggestion}"

def structuredDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  evalTactic tacSeq
  match (← getUnsolvedGoals) with
  | [] => 
    let suggestion ← mkShow (← delab (← oldGoal.getDecl).type) tacSeq
    addTrace `structured m!"Try this: {suggestion}"
  | [newGoal] => 
    let s ← goalsToStateDiff oldGoal newGoal

    match (s.newlyChangedGoal, s.newDecls, s.changedDecls, s.removedDecls) with
    | (none, #[], #[], #[]) => 
      throwError "Unexpected state: no changes before and after tactic evaluation"
    | ((some newGoal), #[], #[], #[]) => 
      let suggestion ← mkSuffices newGoal tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | (none, #[newDecl], #[], #[]) => -- TODO, can you both match on having nonzero newDecls, and name it so we can use it
      let suggestion ← mkHave newDecl tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | (newlyChangedGoal, newDecls, changedDecls, #[]) =>
      let suggestion ← mkNote (newDecls ++ changedDecls) newlyChangedGoal tacSeq
      addTrace `structured m!"Try this: {suggestion}"
    | _ => 
      throwError "Unexpected state: Currently only occurs if any local declaration is lost after tactic evaluation.
                  Removed Declarations: {s.removedDecls.map (fun ldecl => ldecl.type)}"

  | newGoals => 
    structureCasesDefault tacSeq oldGoal newGoals
    pure ()

-- ## Core structured elaboration
def structuredCore (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  match (← getUnsolvedGoals) with
  | [] => 
    logWarning m!"No goals to solve, kind of shouldn't reach this, since we can't execute your tactic anyways"
  | [goal] => 
    let tacs ← getTacs tacSeq
    match tacs with
    | #[] => logWarning "No tactics in tacSeq"
    -- TODO: Match on alternatives of existing structured tactics (from/by, etc)
    | #[t] =>
      match t with
      | `(tactic|suffices $_ by $_) 
      | `(tactic|show $_ by $_) 
      | `(tactic|have $[$id]? : $_ := by $_) 
      | `(tactic|have $[$id]? : $_ := $_) 
      | `(tactic|clear $_)
        => 
        addTrace `structured m!"This tactic is already structured"
        evalTactic tacSeq
      -- TODO: Currently also matches on patterns, probably wrong matching here
      | `(tactic|intro $ids:ident*)
      | `(tactic|intros $ids*)
        => 
        structuredIntros tacSeq goal
      | `(tactic|cases $target:casesTarget)
      -- | `(tactic|induction $target)
        => 
        addTrace `structured m!"Matched on cases or induction, specific implementation"
        structuredCases tacSeq goal target
        -- TEMP: passing to default to test non-specific case expansion
        -- structuredDefault tacSeq goal
      | _ => structuredDefault tacSeq goal
    | _ => structuredDefault tacSeq goal
  | _ =>
    addTrace `structured m!"Multiple goals pre-execution is not supported for this tactic. 
      Executing tacitc, but no suggestions provided"
    evalTactic tacSeq

-- Elaborate tactic
elab &"structured " t:tacticSeq : tactic =>
  structuredCore t

-- TMP Testing code below

example : α → β → α := by  
  -- structured intro
  -- structured intro ha _
  -- structured intro (ha : α) (_ : β)
  -- structured intros
  -- structured intros ha _

  -- TODO: we actually don't want to match on intro patterns, but it still seems to
  structured intro (ha : α) (_ : β)
  -- fix (ha : α) (_ : β) ⊢ α
  exact ha

-- inductive Even : Nat → Prop
-- | zero : Even Nat.zero
-- | add_two : ∀ k : Nat, Even k → Even (k+2) 

-- example (n : Nat) (h : Even n): Even (n + 2) := by
--   structured repeat apply Even.add_two _ _
--   exact h


example (h : α ∧ β) : α ∨ b := by
  structured 
    have ha : α := h.left
    have hb : β := h.right    
    apply Or.intro_left _ ha

example (n : Nat) : n = n := by
  structured cases n
  -- cases n with
  -- | zero => rfl
  -- | succ m => rfl
  -- repeat rfl


example : α ↔ β := by
  -- Is there a way of combining these cases in the application line?
  structured apply Iff.intro
  case mp => sorry
  case mpr => sorry

  -- apply Iff.intro
  -- case mp =>
  --   note ⊢ α → β
  --   sorry
  -- case mpr =>
  --   note ⊢ β → α
  --   sorry

example : α ∧ β → β := by
  intro (⟨ha, hb⟩)