import Lean

open 
  Lean 
  Lean.Meta 
  Lean.Elab 
  Lean.Elab.Tactic
  Lean.PrettyPrinter 
  Lean.Parser 
  Lean.Parser.Tactic

def assertGoal (goalType : TSyntax `term) : TacticM Unit := do
  let realGoalType ← instantiateMVars (← (← getMainGoal).getDecl).type.consumeMData
  let mut expectedGoalType := (← elabTerm goalType none).consumeMData
  if !(realGoalType == expectedGoalType) then
    throwError m!"AssertionError: Expected goal {expectedGoalType}, got {realGoalType}"
  else
    return

elab &"assert_goal " t:term : tactic =>
  assertGoal t

def assertHyp (hypName : Option (TSyntax `ident) := none) (hypType : TSyntax `term) : TacticM Unit := do
  let hypExpr ← elabTerm hypType none
  let mainGoal ← getMainGoal
  let lCtx := (← mainGoal.getDecl).lctx
  match hypName with
  | none => 
    for ldecl in lCtx do
      if ldecl.type.consumeMData == hypExpr.consumeMData then
        addTrace `structured m!"Found it unnamed!"
        return
    throwError m!"Cannot find unnamed hypothesis of type {hypExpr}"
  | some hypName => 
    let hypNameExpr := hypName.getId
    for ldecl in lCtx do
      if ldecl.userName == hypNameExpr then
        if ldecl.type.consumeMData == hypExpr.consumeMData then
          addTrace `structured m!"Found it named!"
          return
        else
          throwError "Found named hypothesis, but types do not match"
    throwError "Cannot find named hypothesis TODO of type TODO"

elab &"assert_hyp " hypName:(ident)? " : " hypType:term : tactic =>
  assertHyp hypName hypType

-- tmp
example : α → α := by
  intro ha
  assert_hyp : α
  assert_hyp ha : α
  -- assert_hyp : α → α -- should fail, no such hypothesis
  -- assert_hyp : β -- should fail, β does not exist
  -- assert_hyp : ha -- should fail, unknown identifier
  
  assert_goal α
  -- assert_goal β -- should fail, β does not exist
  -- assert_goal ha -- should fail, unknown identifier
  -- assert_goal α → α -- should fail, types mismatch

  -- fix (ha : α) ⊢ α
  
  exact ha
-- end tmp

-- Extend tactic version of show to support `by`
macro "show " type:term " by " tacSeq:tacticSeq : tactic => 
  `(exact show $type by $tacSeq)

-- TODO: elab vs macro
elab &"fix " ( "(" hypName:(ident)? ":" hypType:term  ")" )* " ⊢ " newGoal:term : tactic => `(tactic|rfl)


-- macro / elab fix
-- macro / elab structNote

-- Could this even be a macro? Need some way to extract lists of idents and types, though
-- (hyps : Array (Option Ident × Expr))
-- "fix " [[[hypIdent:ident]? " : " hypType:term "]+ ⊢ " newGoal:term
-- => `(tacticSeq| intros hypIdent1 hypIdent2 ..; assertHyp hypIdent1 : hypType1; assertHyp ...; assertGoal newGoal)

-- def fix (hyps : Array (Option Ident × Expr)) (newGoal : Expr) : TacticM Unit := do
--   let a ← `(tactic|sorry) 

-- elab &"fix " : tactic =>
--   fix

-- Structured Annotation
-- `strucNote ($name : $type)* (⊢ $newGoal)? (by $tacSeq)?`
-- execute tacSeq
-- assert all hyps
-- if newGoal, then check that's new goal, else check oldGoal same