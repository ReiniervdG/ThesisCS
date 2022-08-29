import Lean

open
  Lean.Elab.Tactic

-- Extend tactic version of show to support `by`
macro "show " type:term " by " tacSeq:tacticSeq : tactic => `(exact show $type by $tacSeq)


-- def fix : TacticM Unit := do
--   let a ← `(tactic|sorry) 

-- elab &"fix " : tactic =>
--   fix

-- Structured Annotation
-- `strucNote ($name : $type)* (⊢ $newGoal)? (by $tacSeq)?`