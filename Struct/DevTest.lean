import Struct.Struct

set_option pp.rawOnError true
set_option trace.debug true

-- Case testing
-- example (n : Nat) : n > 0 := by
--   structured simp
--   structured cases n 
--   case zero => sorry


example (n : Nat) : true := by
  cases n with
  | zero => 
    rfl
  | succ n => 
    rfl

example (n : Nat) : true := by
  induction n with
  | zero => 
    rfl
  | succ n ih => 
    rfl


-- Already declared in Struct for testing
-- inductive Even : Nat → Prop
-- | zero : Even Nat.zero
-- | add_two : ∀ k : Nat, Even k → Even (k+2) 
