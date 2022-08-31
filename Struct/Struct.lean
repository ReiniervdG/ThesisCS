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

-- TODO: abstract away commonalities between this and other suggestions, like getting goals, extracting info from lCtx
def structuredIntros (tacSeq : TSyntax ``tacticSeq) (hasExplicitNames : Bool) : TacticM Unit := do
  addTrace `structured m!"Matched on intro(s), specific implementation"
  
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getDecl).type

  evalTactic tacSeq

  let newGoal ← getMainGoal
  let newGoalType ← instantiateMVars (← newGoal.getDecl).type

  let isSameGoal := goalType.consumeMData == newGoalType.consumeMData

  let lCtx := (← goal.getDecl).lctx
  let lCtxNew := (← newGoal.getDecl).lctx

  let declsNotInNew := diffLCtx lCtx lCtxNew
  let declsNotInOld := diffLCtx lCtxNew lCtx

  if !isSameGoal ∧ declsNotInNew.size == 0 ∧ declsNotInOld.size > 0 then
    for decl in declsNotInOld do
      addTrace `xx m!"{decl.userName} : {decl.type}, hasExplicitnames: {hasExplicitNames})"
  else
    logWarning "Unexpected state in intros match"

-- TODO: structuredCases / structuredInduction (or same as structuredCases with a boolean or something)

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
        let newStx ← mkHave declStx tacSeq
        addTrace `structured m!"Try this: {newStx}"
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
def structuredCore (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  match (← getUnsolvedGoals) with
  | [] => 
    logWarning m!"No goals to solve, kind of shouldn't reach this, since we can't execute your tactic anyways"
  | [goal] => 
    let tacs ← getTacs tacSeq
    match tacs with
    | #[] => logWarning "No tactics in tacSeq"
    -- TODO: Currently only matching on single tactic, optionally want to allow multiple intro/clear calls
    | #[t] =>
      match t with
      | `(tactic|suffices $_ by $_) 
      | `(tactic|show $_ by $_) 
      | `(tactic|have $_ : $_ := by $_) 
      | `(tactic|clear $_)
        => 
        addTrace `structured m!"This tactic is already structured"
        evalTactic tacSeq
      | `(tactic|intro)
      | `(tactic|intros)
        =>
        structuredIntros tacSeq false
      | `(tactic|intro $id)
      | `(tactic|intros $ids*)
        => 
        structuredIntros tacSeq true
      | `(tactic|cases $target)
      | `(tactic|induction $target)
        => 
        addTrace `structured m!"Matched on cases or induction, specific implementation"
        evalTactic tacSeq
      | _ => structuredDefault tacSeq goal
    | _ => structuredDefault tacSeq goal
  | _ =>
    addTrace `structured m!"Multiple goals pre-execution is not supported for this tactic. 
      Executing tacitc, but no suggestions provided"
    evalTactic tacSeq

-- Elaborate tactic
elab &"structured " t:tacticSeq : tactic =>
  structuredCore t

