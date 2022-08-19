import Struct
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
  induction as
  case nil =>
    simp only [reverse]
    exact pas
  case cons _a _as _ih =>
    simp only [reverse]

    sorry
