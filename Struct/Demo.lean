import Struct.Struct

-- Setup
-- inductive Even : Nat → Prop
-- | zero : Even Nat.zero
-- | add_two : ∀ k : Nat, Even k → Even (k+2) 

inductive Palindrome : List α → Prop
| nil : Palindrome []
| single (a : α) : Palindrome [a]
| sandwich (a : α) (as : List α) (h : Palindrome as) : Palindrome (a::as ++ [a])

def reverse : List α → List α
| [] => []
| a::as => as ++ [a]

/-
  # Custom Tactics Test Cases
-/

-- CT01 : `show .. by` macro expansion
example : 0 = 0 := by
  show 0 = 0 by rfl

-- ## assertGoal
-- CT02 : `assertGoal` succeeds if goal same
example (ha : α) : α := by
  assertGoal α
  assumption
-- CT03 : `assertGoal` fails for unknown `newGoalType`
example (ha : α) : α := by
  -- assertGoal β -- Error: `unknown identifier 'β'`
  assumption
example {α β : Type} (hb : β ) : β := by
  -- assertGoal α -- Error: `AssertionError: Expected goal α, got β`
  assumption

-- ## assertHyp
-- CT04 : Named `assertHyp` succeeds if name and type match
example (ha : α ) : α := by
  assertHyp ha : α
  assumption

-- CT05 : Named `assertHyp` fails if name mismatch (but type in local declarations)
example (ha : α) : α := by
  -- assertHyp ha2 : α -- Error : `TODO`
  assumption

-- CT05 : Named `assertHyp` fails if name match but types different
example (ha : α ) : α := by
  -- assertHyp ha : α ∧ α -- Error : `TODO`
  assumption

-- CT06 : Unnamed `assertHyp` succeeds if type exists in local declarations
example (_ : α) : α := by
  assertHyp : α 
  assumption

-- CT07 : unnamed `assertHyp` fails if type does not exist in local declarations
example {β : Type} (ha : α ) : α := by
  -- assertHyp : β -- Error : `TODO`
  assumption

-- ## fix

-- ## note

/- 
  # Structured Tactic Syntax Match Test Cases
-/

/-
  # Structured Tactic Default Test Cases
-/


-- ### OLD BELOW

example : 0 = 0 := by
  structured rfl
example : 0 = 0 := by
  show 0 = 0 by
    rfl

example : Even 4 := by
  structured repeat apply Even.add_two _ _
  structured apply Even.zero
example : Even 4 := by
  suffices Even 0 by
    repeat 
      apply Even.add_two _ _
    exact this
  show Even 0 by
    apply Even.zero

example : Even 4 := by
  structured 
    repeat apply Even.add_two _ _
    apply Even.zero
example : Even 4 := by
  show Even 4 by
    repeat 
      apply Even.add_two _ _
    apply Even.zero

example (as : List α) (pas : Palindrome as) : Palindrome (reverse as) := by
  structured induction as
  case nil =>
    simp only [reverse]
    exact pas
  case cons _a _as _ih =>
    simp only [reverse]

    sorry

-- example (as : List α) (pas : Palindrome as) : Palindrome (reverse as) := by
--   induction as with
--   | nil => sorry

-- exmaple (n m : Nat) : n < m := by
--   induction m with
--   | succ n => 
-- Use default name, but if it already exist, make it a hole for the user to fill in (maybe with warning)


-- CUSTOM TACTIC TEST CASES
-- Case 1 : Custom show macro `show .. by ..`
-- Case 2 : Intros fix notation `fix (a : _) (b : _) ⊢ c`
-- Case 3 : Custom `difficult` state change
--   a. `strucNote (a : _) (b : _) by c`
--   b. `strucNote (a : _) (b : _) ⊢ c by d`
-- Case 4 : Catch failing `strucNote`s ... TODO

-- Case xx : assert hypotheses and goals
example : α → β → α := by
  -- structured intro (ha : α) hb
  -- intros ha hb
  note (ha : α) (hb : β) ⊢ α by 
    intros ha hb
  show α by
    exact ha

  -- assertHyp : α
  -- assertHyp ha : α
  -- -- assert_hyp : α → α -- should fail, no such hypothesis
  -- -- assert_hyp : β -- should fail, β does not exist
  -- -- assert_hyp : ha -- should fail, unknown identifier
  
  -- assertGoal α
  -- -- assert_goal β -- should fail, β does not exist
  -- -- assert_goal ha -- should fail, unknown identifier
  -- -- assert_goal α → α -- should fail, types mismatch

  -- -- fix (ha : α) ⊢ α
  
  -- exact ha


-- STRUCTURED TEST CASES FROM DIAGRAM
-- Case 1a : Match on show, bracketed
-- example : Even 0 := by
--   structured {
--     show Even 0 by Even.zero
--   }
-- Case 1b : Match on show, indented
example : Even 0 := by
  structured 
    show Even 0 by Even.zero -- note, `show ..  by ..` does not seem to work
  
-- Case 2 : Match on suffices
-- Case 3 : Match on have
-- Case 4 : Match on clear

-- Case 5 : Match on cases ... TODO
-- Case 6 : Match on induction ... TODO

-- Case 7 : Match on intro ... TODO
example : α → α := by
  structured intro
  sorry
example : α → α := by
  structured intro ha
  sorry
-- Case 8 : Match on intros ... TODO
example : α → β → α := by
  structured intros
  sorry
example : α → β → α := by
  structured intros ha hb
  sorry

-- Case 9 : Match on no old goal response (? maybe not possible)
-- Case 10 : Match on multiple old goals response

-- Case 11 : Single old goal, no new goal, suggest show
-- Case 12 : Single old goal, multiple new goals ... (TODO: Warning, or simple cases with tags)

-- Case 13 : Single old/new goal, no change, no ctx change, suggest remove/leave out
-- ... TODO