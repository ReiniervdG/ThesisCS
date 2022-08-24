import Lean

-- Extend tactic version of show to support `by`
macro "show " type:term " by " tacSeq:tacticSeq : tactic => `(exact show $type by $tacSeq)


-- Structured Annotation
-- `strucNote ($name : $type)* (⊢ $newGoal)? (by $tacSeq)?`