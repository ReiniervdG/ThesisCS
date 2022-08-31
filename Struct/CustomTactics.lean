import Lean

open
  Lean.Elab.Tactic

-- Extend tactic version of show to support `by`
macro "show " type:term " by " tacSeq:tacticSeq : tactic => `(exact show $type by $tacSeq)


-- def assertHyp (hypName : Option Ident := none) (hypType : Expr) : TermElabM Unit := sorry
-- def assertGoal (goalType : Expr) : TermElabM Unit := sorry

-- "fix " [[[hypIdent:ident]? " : " hypType:term "]+ ⊢ " newGoal:term
-- => `(tacticSeq| intros hypIdent1 hypIdent2 ..; assertHyp hypIdent1 : hypType1; assertHyp ...; assertGoal newGoal)

-- def fix : TacticM Unit := do
--   let a ← `(tactic|sorry) 

-- elab &"fix " : tactic =>
--   fix

-- Structured Annotation
-- `strucNote ($name : $type)* (⊢ $newGoal)? (by $tacSeq)?`
-- execute tacSeq
-- assert all hyps
-- if newGoal, then check that's new goal, else check oldGoal same