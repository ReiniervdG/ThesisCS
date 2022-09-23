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
    if !newDecl.isAuxDecl then
      let mut foundMatch : Bool := false
      for oldDecl in oldLCtx do
        if !oldDecl.isAuxDecl then
          if newDecl.userName == oldDecl.userName then
            foundMatch := true
            if !(newDecl.type.consumeMData == oldDecl.type.consumeMData) then
              changedDecls := changedDecls.push newDecl
      if !foundMatch then
        newDecls := newDecls.push newDecl

  for oldDecl in oldLCtx do
    if !oldDecl.isAuxDecl then
      let mut foundMatch : Bool := false
      for newDecl in newLCtx do
        if !newDecl.isAuxDecl then
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

def getUniqueIdent : TermElabM (TSyntax `ident) := do
  return mkIdent "tmp0"

def getIdentWithSuggestion (suggestion : name) : TermElabM (TSyntax `ident) := do
  return mkIdent "tmp"

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

-- TODO: Exactly same as induction, except the list of induction names generated and used in result, maybe add bool whether it is included
def structuredCases (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (target : TSyntax `term) (isInduction : Bool) : TacticM Unit :=
  oldGoal.withContext do
    -- For every constructor we need
    -- 1) the name to use in the case statement (e.g. `succ` or `cons`)
    -- 2) the constructor argument idents to be used (e.g. `n` or `someAutoUniqueName`)
    -- 3) if induction, the induction hypothesis idents to be used (e.g. `ih1`, `autoUniqueIHName`)
    let mut cases : Array (TSyntax ``inductionAlt) := #[]

    let myStr : String := "Something"
    let myIdent := mkIdent myStr
    let x ← `(tactic|cases n with | $myIdent => sorry)

    let env ← getEnv

    let targetExpr ← elabTerm target none
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
        
        for ctor in ctors do
          let ctorInfo := env.find? ctor

          match ctor with
          | .str _ s => 
            let ctorIdent := mkIdent s

            match ctorInfo with
            | some (.ctorInfo cval) =>
              addTrace `xx m!"Constructor {ctor} for inductive type {cval.induct}"
              let decls ← forallTelescopeReducing cval.type fun args _ => 
                args.mapM (fun arg => arg.fvarId!.getDecl)

              let mut ctorArgs : Array Ident := #[]
              let mut indArgs : Array Ident := #[]

              for decl in decls do
                if decl.userName.hasMacroScopes then
                  let ctorName ← getUnusedUserName (.str .anonymous "a")
                  ctorArgs := ctorArgs.push (mkIdent ctorName)

                  if isInduction ∧ isAppOf decl.type fnName then
                    let indName ← getUnusedUserName (.str ctorName "ih")
                    indArgs := indArgs.push (mkIdent indName)
                else
                  let ctorName ← getUnusedUserName decl.userName
                  ctorArgs := ctorArgs.push (mkIdent ctorName)

                  if isInduction ∧ isAppOf decl.type fnName then
                    -- Use previous human-readable userIdent and attempt to make that + "ih"
                    let indName ← getUnusedUserName (.str ctorName "ih")
                    indArgs := indArgs.push (mkIdent indName)
              cases := cases.push (← `(inductionAlt| | $ctorIdent $[$ctorArgs]* $[$indArgs]* => sorry))

            | _ => addTrace `xx m!"Unexpected 04"
          | _ => throwError "Unexpected error, constructor has no string name"  

        -- TODO: How to add a `note` statement to a case, outstanding
        let suggestion ← `(tactic| cases $target:term with $[$cases]*)
        addTrace `structured m!"Try this: {suggestion}"

      | _ => 
        addTrace `xx m!"Unexpected error 03"
    | _ => addTrace `xx m!"Unexpected error 02, targetType: {repr targetType}, fnExpr: {repr fnExpr}"

-- def structuredInduction
-- Should be pretty similar to structuredCases, except with a different tacSeq match. Could potentially be combined, depending on construction of match statement

-- structuredCasesDefault: When multiple post-goals, but no match on cases or induction
def structureCasesDefault (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) (newGoals : List MVarId) : TacticM Unit := do
  let mut cases : Array (TSyntax `tactic) := #[]

  -- Construct a case for each new goal
  -- TODO : Move to separate function and use MapM
  for newGoal in newGoals do
    let s ← goalsToStateDiff oldGoal newGoal

    -- Detect inaccessible local context, add to case statement
    -- For each decl in s.newDecls that hasMacroScopes
    let mut caseArgs : Array (TSyntax ``binderIdent) := #[]
    for decl in s.newDecls do
      if decl.userName.hasMacroScopes then
        caseArgs := caseArgs.push (← `(binderIdent|TODO))

    -- Construct change annotation
    -- TODO: Use above caseArg names in this annotation
    let annotation ← mkNote (s.newDecls ++ s.changedDecls) s.newlyChangedGoal none

    -- Construct full case
    let caseIdName := mkIdent (← newGoal.getTag)
    let caseBinderId : TSyntax ``binderIdent ← `(binderIdent|$caseIdName:ident)
    let case ← `(tactic|case $caseBinderId $[$caseArgs]* => 
      $annotation:tactic
      sorry)
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
      -- Matching `suffices` Syntax
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
      | `(tactic|cases $target:term)
      | `(tactic|induction $target:term)
        => 
        addTrace `structured m!"Matched on cases or induction, specific implementation"
        structuredCases tacSeq goal target false -- todo set false or true based on induction
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

inductive Even : Nat → Prop
| zero : Even Nat.zero
| add_two : ∀ k : Nat, Even k → Even (k+2)
| combine_two (k₁ : Nat) (hk1 : Even k₁) : ∀ k₂ : Nat, Even k₂ → Even (k₁ + k₂)

-- example (n : Nat) (h : Even n): Even (n + 2) := by
--   structured repeat apply Even.add_two _ _
--   exact h

example (n : Nat) : n = n := by
  structured induction n
  admit


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
  sorry

example (n : Nat) (h : Even n) : Even (n + n + 2) := by
  structured cases h
  
  -- Make suggestion
  -- match h with
  -- | .zero =>

  --   note ⊢ Even (Nat.zero + Nat.zero + 2)
  --   sorry
  -- | .add_two k autoName =>
  --   note (k : Nat) (autoName : Even k) ⊢ Even (k + 2 + (k + 2) + 2)
  --   sorry
  -- | .combine_two k1 hk1 k2 autoName => 
  --   note (k1 : Nat) (hk1 : Even k1) (k2 : Nat) (autoName : Even k2) ⊢ Even (k1 + k2 + (k1 + k2) + 2)
  --   sorry

  -- For induction make suggestion
  induction h with
  | zero =>
    note ⊢ Even (Nat.zero + Nat.zero + 2)
    sorry
  | add_two k autoName autoNameIH =>
    -- TODO : Add IH annotation
    note (k : Nat) (autoName : Even k) ⊢ Even (k + 2 + (k + 2) + 2)
    sorry
  | combine_two k1 hk1 k2 autoName autoNameIH1 autoNameIH2 => 
    note (k1 : Nat) (hk1 : Even k1) (k2 : Nat) (autoName : Even k2) ⊢ Even (k1 + k2 + (k1 + k2) + 2)
    sorry
  
  -- OR 
  -- cases h
  -- case zero =>
  --   note ⊢ Even (Nat.zero + Nat.zero + 2)
  --   sorry
  -- case add_two k hk =>
  --   note (k : Nat) (hk : Even k) ⊢ Even (k + 2 + (k + 2) + 2)
  --   sorry
  -- case combine_two k1 hk1 k2 hk2 => 
  --   note (k1 : Nat) (hk1 : Even k1) (k2 : Nat) (hk2 : Even k2) ⊢ Even (k1 + k2 + (k1 + k2) + 2)
  --   sorry
  
  -- In case of induction, for each inductive type, we have to add some `ih` to the end of args
  -- induction h
  -- case combine_two k1 k2 hk1 hk2 ih1 ih2 => 

-- Realization, question 1: We need an argument for each `forallE` in the Expr tree
-- Note 2: How do we know if something is inductive? ctor has info, but not for how many args are inductive
-- Note 3: Something with forallTelescope, need to understand first


example (n : Nat) : α ↔ β := by
  -- TODO currently the binderDecl (ha → ?a) contains an uninstantiated var

  structured 
    apply Iff.intro
    intro ha
  case mp => sorry
  case mpr => sorry

  -- apply Iff.intro
  -- case mp =>
  --   note ⊢ α → β
  --   sorry
  -- case mpr =>
  --   note ⊢ β → α
  --   sorry

example (n : Nat) : n = n := by
  structured 
    cases n
    try apply Even.zero
  admit

example : α ∧ β → β := by
  -- structured intro (⟨ha, hb⟩) 
  
  note (ha : α) (hb : β) ⊢ β by intro (⟨ha, hb⟩)
  sorry
