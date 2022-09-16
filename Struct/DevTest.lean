import Struct.Struct

set_option pp.rawOnError true
set_option trace.debug true

example : α → β ∧ γ → α ∧ β := by
  intros ha hbg
  have hb : β := hbg.left
  exact And.intro ha hb

example : α → β ∧ γ → α ∧ β := by
  fix (ha : α) (hbg : β ∧ γ) ⊢ α ∧ β -- fix always uses intros
  have hb : β := hbg.left
  exact And.intro ha hb

example : α → β ∧ γ → α ∧ β := by
  note (ha : α) (hbg : β ∧ γ) (hb : β) ⊢ α ∧ β by
    intros ha hbg
    have hb : β := hbg.left
  exact And.intro ha hb

example : α → β ∧ γ → α ∧ β := by
  intros ha hbg
  have hb : β := hbg.left
  show α ∧ β by 
    exact And.intro ha hb


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
