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


def structured (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  -- TODO: Only do something if a an option is turned on
  -- TODO: Then prepend structured before any tactic execution

  -- TODO: Match on all our structures, ignore the rest
  -- match tacSeq with
  -- | `(tacticSeq|suffices $_ by $_) 
  -- | `(tacticSeq|show $_ by $_) 
  -- | `(tacticSeq|have $_ : $_ := by $_) 
  --   => 
  --   addTrace `structured m!"This tactic is already structured"
  --   evalTactic tacSeq
  -- | _ => 
  match (← getUnsolvedGoals) with
  | [] => 
    logWarning m!"No goals to solve, kind of shouldn't reach this, since we can't execute your tactic anyways"
  | [goal] => 
    let goalType ← instantiateMVars (← goal.getDecl).type
    evalTactic tacSeq
    match (← getUnsolvedGoals) with
    | [] => 
      let goalStx ← delab goalType
      let stx ← `(tactic|
        show $goalStx by 
          $tacSeq)
      addTrace `structured m!"Try this: {stx}"
    | [newGoal] => 
      let newGoalType ← instantiateMVars (← newGoal.getDecl).type
      let isSameGoal := goalType.consumeMData == newGoalType.consumeMData

      let lCtx := (← goal.getDecl).lctx
      let lCtxNew := (← newGoal.getDecl).lctx

      let declsNotInNew := diff_lctx lCtx lCtxNew
      let declsNotInOld := diff_lctx lCtxNew lCtx

      if !isSameGoal && declsNotInNew.size = 0 && declsNotInOld.size = 0 then
        let newGoalStx ← delab (← instantiateMVars newGoalType)
        let newStx ← `(tactic|
          suffices $newGoalStx by 
            $tacSeq:tacticSeq;
            exact this)
        addTrace `structured m!"{newStx}"
      else if h : isSameGoal ∧ declsNotInNew.size = 0 ∧ declsNotInOld.size = 1 then
        -- Prove that we know we can use the first index
        have : 0 < declsNotInOld.size := by simp_all
        let decl := declsNotInOld[0]
        let newDeclStx ← delab decl.type
        -- NOTE: this stx does not really make sense, because from what I understand it can only happen if there is already a have clause
        let newStx ← `(tactic|
          have : $newDeclStx := by 
            $tacSeq)
        addTrace `structured m!"Try this: {newStx}"
      else
        -- temp investigating types
        let lCtx : LocalContext := (← goal.getDecl).lctx
        for (decl : LocalDecl) in lCtx do
          addTrace `structured m!"Decl Type : {decl.type}"
          -- REALLY hacky way of ensuring we have the right decl we want to find constructors of
          if toString decl.type == "Nat" then
            let t : Expr := decl.type
            addTrace `structured m!"Type Expression : {t}"
            addTrace `structured m!"Expression Constructor : {Lean.Expr.ctorName t}"
            match t with
            | .const n us =>
              addTrace `structured m!"Expression construcion with name : {n} and us {us}"
            | _ =>
              addTrace `structured m!"other"

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
      for newGoal in newGoals do
        let newGoalType ← instantiateMVars (← newGoal.getDecl).type
        addTrace `structured m!"MVarId.name : {newGoal.name}"
        addTrace `structured m!"← MVarId.getTag : {(← newGoal.getTag)}"
        addTrace `structured m!"new goal : {newGoalType}}"
        let tag ← newGoal.getTag
        let tmpStx ← `(tactic|
          case $(TSyntax.mk <| mkIdent tag) => 
            rfl)
        addTrace `structured m!"Case stx: {tmpStx}"
      -- end temp

  | goal::moreGoals =>
    let goalDecl ← goal.getDecl
    logWarning m!"Multiple goals pre-execution. This tactic may not work as expected if multiple goals change. Currently unimplemented"
    evalTactic tacSeq

-- Elaborate tactic
elab &"structured " t:tacticSeq : tactic =>
  structured t