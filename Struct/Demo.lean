import Struct.Struct
import Struct.CustomTactics

-- Setup
inductive Even : Nat → Prop
| zero : Even Nat.zero
| add_two : ∀ k : Nat, Even k → Even (k+2) 

inductive Palindrome : List α → Prop
| nil : Palindrome []
| single (a : α) : Palindrome [a]
| sandwich (a : α) (as : List α) (h : Palindrome as) : Palindrome (a::as ++ [a])

def reverse : List α → List α
| [] => []
| a::as => as ++ [a]


example : 0 = 0 := by
  structured rfl
  rfl
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


-- STRUCTURED TEST CASES FROM DIAGRAM
-- Case 1a : Match on show, bracketed
-- example : Even 0 := by
--   structured {
--     show Even 0 by Even.zero
--   }
-- Case 1b : Match on show, indented
example : Even 0 := by
  structured 
    show Even 0 by Even.zero
  
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