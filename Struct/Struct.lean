import Lean

import Struct.Helpers
import Struct.CustomTactics

open 
  Lean 
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

/-
  # Description of this file ..

  -- MAIN TODO for now: Revamp comparison of MVarIds, also checking userNames, consider cleared / changed / added decls, maybe a new type for it?
-/

-- ## Helpers ..
def declToBinder (decl : LocalDecl) : TermElabM (TSyntax `strucBinder) := do
  if decl.userName.hasMacroScopes then
    return (← `(strucBinder|(_ : $(← delab decl.type))))
  else 
    return (← `(strucBinder|($(mkIdent decl.userName) : $(← delab decl.type))))

-- TODO: Consolidate some logic about comparing goals and local contexts, bit tough especially in its intended return type, maybe a custom structure?
-- def diffGoals (oldGoal : MVarId) (newGoal : MVarId) : TermElabM Unit := do
--   let oldGoalType ← instantiateMVars (← oldGoal.getDecl).type
--   let newGoalType ← instantiateMVars (← newGoal.getDecl).type
--   let isSameGoal := oldGoalType.consumeMData == newGoalType.consumeMData

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

def mkNote (decls : Array LocalDecl := #[]) (optGoal : Option Term := none) (tacSeq : TSyntax ``tacticSeq) : TermElabM (TSyntax `tactic) := do
  let binders ← decls.mapM (fun decl => declToBinder decl)  
  match optGoal with
  | some goal => `(tactic|note $[$binders]* ⊢ $goal by $tacSeq)
  | none => `(tactic|note $[$binders]* by $tacSeq)

def mkCases (x : TSyntax ``casesTarget) (y : TSyntax ``binderIdent) : TermElabM (TSyntax ``tacticSeq) := do
  `(tacticSeq|
    cases $x
    case $y =>
      rfl)

-- def mkInduction

-- def mkAutoCases

-- ## Structured branches
def structuredIntros (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  evalTactic tacSeq
  match (← getUnsolvedGoals) with
  | [] => throwError "Finishing with intros should be impossible"
  | [newGoal] => 
    let oldGoalType ← instantiateMVars (← oldGoal.getDecl).type
    let newGoalType ← instantiateMVars (← newGoal.getDecl).type
    let isSameGoal := oldGoalType.consumeMData == newGoalType.consumeMData

    let oldLCtx := (← oldGoal.getDecl).lctx
    let newLCtx := (← newGoal.getDecl).lctx

    let removedDecls := diffLCtx oldLCtx newLCtx
    let addedDecls := diffLCtx newLCtx oldLCtx  

    if !isSameGoal ∧ removedDecls.size == 0 ∧ addedDecls.size > 0 then
      let fixTac ← mkFix addedDecls (← delab newGoalType)
      addTrace `structured m!"Try this: {fixTac}"
    else
      throwError "Unexpected state in intros match"
  | _ => throwError "Having multiple goals post-intros should be impossible"

-- def structuredCases

-- def structuredInduction

-- structuredCasesDefault: When multiple post-goals, but no match on cases or induction
-- def structuredCasesDefault

def structuredDefault_tmp (tacSeq : TSyntax ``tacticSeq) (oldGoal : MVarId) : TacticM Unit := do
  evalTactic tacSeq
  match (← getUnsolvedGoals) with
  | [] => 
    let suggestion ← mkShow (← delab (← oldGoal.getDecl).type) tacSeq
    addTrace `structured m!"Try this: {suggestion}"
  | [newGoal] => 
    -- TODO: REVAMP CTX COMPARISON
    -- Do something interesting, given old and new MVarId

    let oldGoalType ← instantiateMVars (← oldGoal.getDecl).type
    let newGoalType ← instantiateMVars (← newGoal.getDecl).type
    let isSameGoal := oldGoalType.consumeMData == newGoalType.consumeMData

    addTrace `test m!"{isSameGoal} : {oldGoalType} : {newGoalType}"

    let oldLCtx := (← oldGoal.getDecl).lctx
    let newLCtx := (← newGoal.getDecl).lctx

    let removedDecls := diffLCtx oldLCtx newLCtx
    let addedDecls := diffLCtx newLCtx oldLCtx

    -- Currently we do check for removedDecls, but in reality we don't really know what to do with them in current notation.
    if removedDecls.size > 0 then
    logWarning m!"That combination of changes in goals and local declarations is currently unsupported, how to handle removed declarations? 
              isSameGoal, old, new: {isSameGoal} {oldGoalType} {newGoalType}
              Removed Declarations: {removedDecls.size} {removedDecls.map (fun x => x.type)} 
              Added Declarations: {addedDecls.size} {addedDecls.map (fun x => x.type)}"
    else 
      if !isSameGoal ∧ addedDecls.size == 0 then
        let suggestion ← mkSuffices (← delab newGoalType) tacSeq
        addTrace `structured m!"Try this: {suggestion}"
      else if isSameGoal ∧ addedDecls.size == 1 then
        let newDecl := addedDecls[0]!
        let suggestion ← mkHave newDecl tacSeq
        addTrace `structured m!"Try this: {suggestion}"
      else
        match isSameGoal with
        | true => 
          let suggestion ← mkNote addedDecls none tacSeq
          addTrace `structured m!"Try this: {suggestion}"
        | false =>
          let suggestion ← mkNote addedDecls (some (← delab newGoalType)) tacSeq
          addTrace `structured m!"Try this: {suggestion}"

  | newGoals => 
    addTrace `structured m!"tmp"  
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
      | `(tactic|intro $ids:ident*)
      | `(tactic|intros $ids*)
        => 
        structuredIntros tacSeq goal
      | `(tactic|cases $target)
      | `(tactic|induction $target)
        => 
        addTrace `structured m!"Matched on cases or induction, specific implementation"
        evalTactic tacSeq
      | _ => structuredDefault_tmp tacSeq goal
    | _ => structuredDefault_tmp tacSeq goal
  | _ =>
    addTrace `structured m!"Multiple goals pre-execution is not supported for this tactic. 
      Executing tacitc, but no suggestions provided"
    evalTactic tacSeq

-- Elaborate tactic
elab &"structured " t:tacticSeq : tactic =>
  structuredCore t

-- ## TODO: Restructure old below

def structuredDefault (tacSeq : TSyntax ``tacticSeq) (goal : MVarId) : TacticM Unit := do
    let goalType ← instantiateMVars (← goal.getDecl).type
    evalTactic tacSeq
    match (← getUnsolvedGoals) with
    | [] => 
      let goalStx ← delab goalType
      let stx ← mkShow goalStx tacSeq
      addTrace `structured m!"Try this: {stx}"
    | [newGoal] => 
      let newGoalType ← instantiateMVars (← newGoal.getDecl).type
      let isSameGoal := goalType.consumeMData == newGoalType.consumeMData

      let lCtx := (← goal.getDecl).lctx
      let lCtxNew := (← newGoal.getDecl).lctx

      let declsNotInNew := diffLCtx lCtx lCtxNew
      let declsNotInOld := diffLCtx lCtxNew lCtx

      if !isSameGoal && declsNotInNew.size = 0 && declsNotInOld.size = 0 then
        let newGoalStx ← delab (← instantiateMVars newGoalType)
        let stx ← mkSuffices newGoalStx tacSeq
        addTrace `structured m!"Try this: {stx}"
      else if h : isSameGoal ∧ declsNotInNew.size = 0 ∧ declsNotInOld.size = 1 then
        -- Prove that we know we can use the first index
        have : 0 < declsNotInOld.size := by simp_all
        let decl := declsNotInOld[0]
        let declStx ← delab decl.type
        -- NOTE: this stx does not really make sense, because from what I understand it can only happen if there is already a have clause
        -- let newStx ← mkHave decl declStx tacSeq
        -- addTrace `structured m!"Try this: {newStx}"
      else
        -- temp investigating types
        -- let lCtx : LocalContext := (← goal.getDecl).lctx
        -- for (decl : LocalDecl) in lCtx do
        --   addTrace `structured m!"Decl Type : {decl.type}"

        --   -- Something with ConstantInfo, inductInfo

        --   -- REALLY hacky way of ensuring we have the right decl we want to find constructors of
        --   if toString decl.type == "Nat" then
        --     let t : Expr := decl.type
        --     addTrace `structured m!"Type Expression : {t}"
        --     addTrace `structured m!"Expression Constructor : {Lean.Expr.ctorName t}"
        --     match t with
        --     | .const n us =>
        --       addTrace `structured m!"Expression construcion with name : {n} and us {us}"
        --       let x := (← getEnv).find? n
        --       match x with 
        --       | some (.inductInfo ival) => 
        --         let ctors := ival.ctors
        --       | _ => return

        --     | _ =>
        --       addTrace `structured m!"other"

            -- TODO: how to get the existing known constructors of the const Nat
            
            -- Borrowed from Ed Ayers, but is not a match statement, doesnt use info on the type
            -- let stx ← `(tactic| cases $(TSyntax.mk <| mkIdent localDecl.userName))

        -- end
        logWarning m!"That combination of changes in goals and local declarations is currently unsupported 
                      isSameGoal: {isSameGoal} {goalType} {newGoalType}
                      NotInNew: {declsNotInNew.size} {declsNotInNew.map (fun x => x.type)} 
                      NotInOld: {declsNotInOld.size} {declsNotInOld.map (fun x => x.type)}"

    | newGoals => 
      logWarning m!"Multiple goals after tactic execution, TODO to implement a case distinction suggestion"
      -- temp for investigating case autocomplete
      -- let mut cases := #[]

      -- for newGoal in newGoals do
      --   let tag ← newGoal.getTag
      --   let tseq ← `(tacticSeq|sorry)
      --   let caseStx ← `(tactic|
      --     case $(TSyntax.mk <| mkIdent tag):ident =>
      --       $tseq:tacticSeq)
      --   cases := cases.push caseStx
      
      -- -- TODO: Find neat way of unpacking cases
      -- -- let firstCase := $cases[0]!
      -- -- let allStx ← `(tacticSeq|
      -- --   $tacSeq;
      -- --   $firstCase)

      -- addTrace `structured m!"All Case Syntax combined : TODO"
      -- -- end temp

-- structured core, mainly matches on pre-goals and input syntax, redirects to respective suggestions


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

example (n : Nat) (h : Even n): Even (n + 2) := by
  structured repeat apply Even.add_two _ _
  exact h


example (h : α ∧ β) : α ∨ b := by
  structured 
    have ha : α := h.left
    have hb : β := h.right    
    apply Or.intro_left _ ha
