


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
| a::as => (reverse as) ++ [a]

-- theorem reverseAppend (as : List α) (a : α) : (reverse as) ++ a → reverse (a::as)
-- | xs x => sorry

example (as : List α): reverse (reverse as) = as := by
  cases as with
  | nil => 
    repeat rw [reverse]
  | _ => sorry

example : 1 + 0 = 1 := by
  apply Nat.add_zero


example (n : Nat) (h : Even n) : Even (n + 2) := by
  show Even (n + 2) 
  . apply Even.add_two _ h

example (n m : Nat) (hm: m = 0) (h : Even (n + m)) : Even (n + m + 2) := by
  rw [hm] at *
  simp at h ⊢
  sorry
  
example (n : Nat) : Even n ↔ Even (n + 2) := by
  apply Iff.intro
  case mp => intro h ; apply Even.add_two _ h
  case mpr =>
    intro h
    sorry

example {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by  
  apply Iff.intro
  all_goals intro _
  case mp a =>
    -- note (a : p → q) ⊢ ¬q → ¬p

  case mpr a =>
    -- note (a : ¬q : ¬p) ⊢ p → q


-- example {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by  
--   apply Iff.intro
--   all_goals intro h
--   . intro hnq
--     rw [Not] at *


-- Example of existing structures
-- example (hab : α ∧ β) : β ∨ α := by
--   exact Or.intro_right _ hab.left

-- example (ha : α) : α := by
--   have this : α := sorry
--   suffices α ∧ α by
--     suffices α ∨ α by
--       sorry
--     skip

example (hab : α ∧ β) : β ∨ α := by
  have ha : α := by exact hab.left
  suffices α by
    apply Or.intro_right _ _
    exact this
  show α
  . exact ha
  
-- Example of intro, intros
example : α₁ → α₂ ∧ α₃ → α₄ ∧ α₅ → α₆ ∧ α₇ → α₁ := by
  intro ha1
  -- Before
  intro (ha23 : α₂ ∧ α₃) _ (⟨ (ha6 : α₆), ha7⟩)
  -- After
  -- intro (ha23 : α₂ ∧ α₃) _ (⟨ (ha6 : α₆), ha7⟩) ⊢ α₁
  exact ha1

example : α₁ → α₂ ∧ α₃ → α₁ := by
  -- -- Before
  -- intro _ _
  -- -- After
  -- intro (autoName1 : α₁) (autoName2 : α₂ ∧ α₃) ⊢ α₁ 
  -- intro h1 ⟨h2, _⟩
  intro (h1 : α₁) (⟨h2, autoName1⟩ : α₂ ∧ α₃) -- TODO


-- Example of multiple goals
example : α ↔ α := by
  apply Iff.intro
  case mp => intro ha ; exact ha
  case mpr =>  intro ha ; exact ha

-- Issue with multiple goals
example : α ↔ α := by 
  apply Iff.intro
  focus
    intro ha
    exact ha
  repeat {intro ha ; exact ha}



-- Example of induction
example (n : Nat) : n < n + 1 := by
  induction n
  repeat sorry
example (n : Nat) : n < n + 1 := by
  induction n 
  case zero => sorry
  case succ m m.ih => sorry
example (n : Nat) : n < n + 1 := by
  induction n with
  | zero => sorry
  | succ m m.ih => sorry

example : α ↔ α := by
  apply Iff.intro 
  show α → α
  . sorry
  repeat sorry


-- example : α ↔ α := by
--   apply Iff.intro  
--   case mp _ => note _ ; skip
--   case mpr => skip

  
  -- State
  -- Goal 1, case mp
    -- α : Prop ⊢ α → α
  -- Goal 2, case mpr 
    -- α : Prop ⊢ α → α
    -- sorry
    -- sorry
  -- { sorry }
    -- sorry
  -- . sorry

example : α ↔ β := by
  apply Iff.intro
  show α → β
  repeat sorry

-- CD01 - Changed context example
example (ha : α) : α ∨ β := by
  -- State: {α β : Prop, ha : α ⊢ α ∨ β }
  apply Or.intro_left _ _
  -- State: {α β : Prop, ha : α ⊢ α }
  sorry
example (ha : α) : α ∨ β := by
  suffices α by
    apply Or.intro_left _ _
    exact this
  sorry

example (hab : β ∧ α) : α ∧ β := by
  apply And.intro hab.right _
  sorry

example (n : Nat) : n = n := by
  cases n <;> rfl
  
example : Even 6 := by
  repeat apply Even.add_two _ _
  sorry


example (ha : α) : α := by
  show α
  . exact ha

example (ha : α) : α ∨ α := by
  suffices α by
    apply Or.intro_left _ _
    exact this
  sorry

example (hab : α ∧ β) : α := by
  have ha : α := by 
    apply hab.left
  sorry

example {α : Prop} :  α → β → α := by
  -- State {α : Prop ⊢ α → α}
  intros
  -- State {α : Prop, ha : α ⊢ α}
  assumption


-- example (ha : α) : α := by
--   show α by
  -- .  exact ha


-- example : α → α  ↔ α := by
--   apply Iff.intro
--   intro _
--   case mp h => sorry

-- example (n : Nat) : n = n := by
--   induction n with
--   | zero => ?_
--   | succ => ?_
--   sorry

-- DESIGN EXAMPLES BELOW

-- example (ha : α) : α := by
--   exact ha
-- example (ha : α) : α := by
--   show α by 
--     exact ha

-- example (ha : α) : α ∨ β := by
--   apply Or.intro_left _ _
-- example (ha : α) : α ∨ β := by
--   suffices α by
--     apply Or.intro_left _ _
--     exact this
  
-- TODO: if it is unnamed or untyped, still throw it through suggestions with $rhs same
-- example (hab : α ∧ β) : α := by
--   have := hab.left
-- example (hab : α ∧ β) : α := by
--   have ha : α := hab.left

-- example (hab : α ∧ β) : β ∧ α := by
--   have ha : α := hab.left
--   apply And.intro _ ha
-- example (ha : α) : α ∧ β ∧ α := by
--   note (ha : α) ⊢ β by 
--     have ha : α := hab.left
--     apply And.intro _ ha
  
example : α ↔ α := by
  apply Iff.intro
  -- State:
  -- Case mp {α : Prop ⊢ α → α}
  -- Case mpr {α : Prop ⊢ α → α}
  repeat intro ha ; exact ha
example : α ↔ α := by
  apply Iff.intro
  case mp =>
    intro ha ; exact ha
  case mpr =>
    intro ha ; exact ha

example : α ↔ α := by
  apply Iff.intro
  all_goals intro ha
  -- State:
  -- Case mp {α : Prop, ha : α ⊢ α → α}
  -- Case mpr {α : Prop, ha : α ⊢ α → α}
  repeat exact ha
example : α ↔ α := by
  apply Iff.intro
  all_goals intro _
  case mp ha =>
    exact ha
  case mpr ha =>
    exact ha

-- example : α ↔ α := by
--   apply Iff.intro
--   all_goals intro _
--   case mp ha =>
--     show (ha : α) ⊢ α
--     exact ha
--   case mpr ha =>
--     show (ha : α) ⊢ α
--     exact ha

-- TODO: These cases don't have tags, then use underscore?
example : Even 6 ∧ Even 4 := by
  apply And.intro _ _
  all_goals repeat apply Even.add_two _ _

  case _ => sorry
  case _ => sorry


-- INTROS EXAMPLES
-- Singles
example : α → α := by
  -- Adding inaccessible hypothesis
  intro
  intro _
  intros
  -- Adding named hypothesis
  intro ha
  intros ha

-- Multiple
example : α → β → α := by
  -- Adding inaccssible hypotheses
  intro _ _
  intros
  -- Adding named hypotheses
  intro ha hb
  intros ha hb

-- Pattern matching
example : α → α ∧ β → α := by
  intro (ha : α) (⟨ (ha : α ), (hb : β) ⟩)

-- TODO: Determine whether an intros statement contains inaccssible decls, warn user, leave out annotation ?

-- CASES EXAMPLES
-- Natural example: reverse of palindrome is itself a palindrome
example (as : List α) (h : Palindrome as) : Palindrome (reverse as) := by
  cases h with
  | nil => 
    simp [reverse]
    exact Palindrome.nil
  | single a => 
    simp [reverse]
    exact Palindrome.single _
  | sandwich a as has => 
    simp [reverse]
    sorry
    

-- Intro code examples
example (n m : Nat) : Even n ∧ Even m → Even 0 → Even (n + m) := by 
  -- intro
  -- intro _ 
  -- intro hnm
  -- intros _
  -- intro hnm _
  -- intros
  -- intros hm _
  -- intro ⟨hn, _⟩ _

  -- intro (a : Even n ∧ Even m)
  -- intro (a : Even n ∧ Even m)
  -- intro (hnm : Even n ∧ Even m)
  -- intro (a : Even n ∧ Even m)
  -- intro (hnm : even n ∧ Even m) (a : Even 0)
  -- intro (a : Even n ∧ Even m) (a.1 : Even 0)
  -- intro (hm : Even n ∧ Even m) (a : Even 0)
  -- intro (⟨hn, _ ⟩ : Even n ∧ Even m) (a : Even 0)

  sorry
