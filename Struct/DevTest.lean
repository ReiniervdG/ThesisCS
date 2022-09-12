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
    sorry
  | succ n => 
    sorry

example (n : Nat) : true := by
  induction n with
  | zero => 
    sorry
  | succ n ih => 
    sorry

example : α → α := by
  intro
  -- fix (ha : α) ⊢ α
  sorry
example : α → α := by
  intro ha
  -- fix (ha : α) ⊢ α
  sorry
example : α → α := by
  intros
  -- fix (ha : α) ⊢ α
  sorry
example : α → β → α := by
  intros ha hb
  -- fix (ha : α) (hb : β) ⊢ α
  sorry

inductive Even : Nat → Prop
| zero : Even Nat.zero
| add_two : ∀ k : Nat, Even k → Even (k+2) 

-- example : Even 0 := by
--   structured 
--     show Even 0 by apply Even.zero

-- import Lean
open 
  Lean.Elab.Tactic
  in
-- Warning: uses sorry
def testTactic : TacticM Unit := do
  let tac ← `(tactic|rfl)
  match tac with
  | `(tactic|rfl) =>
    evalTactic tac
  | _ => 
    sorry
  evalTactic tac

elab &"testTactic" : tactic =>
  testTactic

example {α : Type} : true := by
  -- Error: tactic 'tacticTestTactic' has not been implemented
  have ha : α := by sorry
  rfl