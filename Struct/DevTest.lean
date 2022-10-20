-- Setup

inductive Even : Nat → Prop
| zero : Even Nat.zero
| add_two : ∀ k : Nat, Even k → Even (k+2) 

-- Example of existing structures
example (hab : α ∧ β) : β ∨ α := by
  exact Or.intro_right _ hab.left

example (ha : α) : α := by
  show α
  . skip 
    exact ha

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
  intro (ha23 : α₂ ∧ α₃) ha45 (⟨ (ha6 : α₆), ha7⟩)
  exact ha1

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

example (n : Nat) : n = n := by
  induction n with
  | zero => ?_
  | succ => ?_
  sorry

