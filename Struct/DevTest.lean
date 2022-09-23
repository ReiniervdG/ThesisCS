import Struct.Struct

set_option pp.rawOnError true
set_option trace.debug true

-- Try to get LoVe Hoare logic definition and lemma to Lean 4

namespace LoVe

def state : Type :=
  String → Nat
def state.update (name : String) (val : Nat) (s : state) : state := 
  fun name' => if name' = name then val else s name'
notation s " { " name " ↦ " val " } " => state.update name val s

inductive stmt : Type
| skip   : stmt
| assign : String → (state → Nat) → stmt
| seq    : stmt → stmt → stmt
| ite    : (state → Prop) → stmt → stmt → stmt
| while_tmp  : (state → Prop) → stmt → stmt
infixl:90 " ;; " => stmt.seq

inductive big_step : stmt → state → state → Prop
| skip {s} :
  big_step stmt.skip s s
| assign {x a s} :
  big_step (stmt.assign x a) s (s{x ↦ a s})
| seq {S T s t u} (hS : big_step S s t)
    (hT : big_step T t u) :
  big_step (S ;; T) s u
| ite_true {b : state → Prop} {S T s t} (hcond : b s)
    (hbody : big_step S s t) :
  big_step (stmt.ite b S T) s t
| ite_false {b : state → Prop} {S T s t} (hcond : ¬ b s)
    (hbody : big_step T s t) :
  big_step (stmt.ite b S T) s t
| while_true {b : state → Prop} {S s t u} (hcond : b s)
    (hbody : big_step S s t)
    (hrest : big_step (stmt.while_tmp b S) t u) :
  big_step (stmt.while_tmp b S) s u
| while_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  big_step (stmt.while_tmp b S) s s
infix:110 " ⟹ " => big_step

-- NOTE: cannot do induction on hl if it's made with stmt × state and infix ⟹
-- Then we get error `index in target type not a variable, (S, s)`
theorem big_step_deterministic {S s l r} (hl : big_step S s l) (hr : big_step S s r) : l = r := by
  induction hl 
  case skip => 
    cases hr
    rfl
  case assign =>
    cases hr
    rfl
  case seq S T s t l hS hT ihS ihT =>
    cases hr
    admit -- TODO
  case ite_true b S T s t hb hS ih =>
    cases hr
    case ite_true x1 x2 x3 x4 => 
      apply ih x4 -- In lean 3, after using `cases' hr`, they still use `hr` at the underscore. In Lean 4 `hr` does not exist anymore
    case ite_false =>
      admit -- cc
  case ite_false b S T s t hb hT ih =>
    cases hr
    case ite_true =>
      admit -- cc
    case ite_false x1 x2 x3 x4 =>
      apply ih x4
  case while_true b S s t u hb hS hw ihS ihw =>
    cases hr
    case while_true x1 x2 x3 x4 x5 x6 =>
      admit -- bit weird 
      -- cases ihS _
      -- cases ihw _
      -- rfl
    case while_false =>
      admit -- cc
  case while_false =>
    cases hr
    case while_true =>
      admit -- cc
    case while_false =>
      rfl

@[simp] theorem big_step_skip_iff {s t} : big_step stmt.skip s t ↔ t = s := by
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | skip => rfl
  case mpr =>
    intro h
    admit
    --exact big_step.skip _ _


-- def partial_hoare (P : state → Prop) (S : stmt) (Q : state → Prop) : Prop := 
--   ∀ s t, P s → (S, s) ⟹ t → Q t

-- notation:110 " {* " P " *} " S " {* " Q " *} " => partial_hoare P S Q

-- theorem skip_intro {P : state → Prop} : {* P *} stmt.skip {* P *} := by
--   rw [partial_hoare]
--   intros s t hs hst
--   cases hst
--   assumption

-- def while_intro (P : state → Prop) {b : state → Prop} {S}
--   (h : {* fun s => P s ∧ b s *} S {* P *}) :
--   {* P *} stmt.while_tmp b S {* fun s => P s ∧ ¬ b s *} := by
--     intros s t hs hst
    
--     admit -- TODO

-- def while_intro' {b P Q : state → Prop} {S}
--     (I : state → Prop)
--     (hS : {* fun s => I s ∧ b s *} S {* I *})
--     (hP : ∀s, P s → I s)
--     (hQ : ∀s, ¬ b s → I s → Q s) :
--   {* P *} stmt.while_tmp b S {* Q *} := by admit -- proof omitted

-- def ADD : stmt :=
-- stmt.while_tmp (fun s => s "n" ≠ 0)
--   (stmt.assign "n" (fun s => s "n" - 1) ;;
--    stmt.assign "m" (fun s => s "m" + 1))

-- -- TODO, can't get `while_intro'` to work
-- -- theorem ADD_correct (n₀ m₀ : Nat) :
-- --   {* fun s => s "n" = n₀ ∧ s "m" = m₀ *}
-- --   ADD
-- --   {* fun s => s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
-- --   while_intro (fun s : state => s "n" + s "m" = n₀ + m₀)
-- --   by admit

-- inductive small_step : stmt × state → stmt × state → Prop
-- | assign {x a s} :
--   small_step (stmt.assign x a, s) (stmt.skip, s{x ↦ a s})
-- | seq_step {S S' T s s'} (hS : small_step (S, s) (S', s')) :
--   small_step (S ;; T, s) (S' ;; T, s')
-- | seq_skip {T s} :
--   small_step (stmt.skip ;; T, s) (T, s)
-- | ite_true {b : state → Prop} {S T s} (hcond : b s) :
--   small_step (stmt.ite b S T, s) (S, s)
-- | ite_false {b : state → Prop} {S T s} (hcond : ¬ b s) :
--   small_step (stmt.ite b S T, s) (T, s)
-- | while {b : state → Prop} {S s} :
--   small_step (stmt.while_tmp b S, s)
--     (stmt.ite b (S ;; stmt.while_tmp b S) stmt.skip, s)

-- infixr:60 " ⇒ " => small_step


-- example : ¬ p := by

-- -- Maybe small step semantics better, larger proofs and can do pretty nice annotations here without too much custom notation
-- theorem small_step_final (S s) :
--   (¬ ∃T t, (S, s) ⇒ (T, t)) ↔ S = stmt.skip := by 
--   induction S with 
--   | skip =>
--     simp [Not]
--     intros T t hst
--     admit

--   | assign x a => 
--     simp [Not]
--     apply Exists.intro (fun x => false)
--   | seq S T ihS ihT => sorry
--   | ite b S T ihS ihT => sorry
--   | while_tmp b S ih => sorry
    
-- begin
--   induction' S,
--   case skip {
--     simp,
--     intros T t hstep,
--     cases' hstep },
--   case assign : x a {
--     simp,
--     apply exists.intro stmt.skip,
--     apply exists.intro (s{x ↦ a s}),
--     exact small_step.assign },
--   case seq : S T ihS ihT {
--     simp,
--     cases' classical.em (S = stmt.skip),
--     case inl {
--       rw h,
--       apply exists.intro T,
--       apply exists.intro s,
--       exact small_step.seq_skip },
--     case inr {
--       simp [h, auto.not_forall_eq, auto.not_not_eq] at ihS,
--       cases' ihS s with S' hS',
--       cases' hS' with s' hs',
--       apply exists.intro (S' ;; T),
--       apply exists.intro s',
--       exact small_step.seq_step hs' } },
--   case ite : b S T ihS ihT {
--     simp,
--     cases' classical.em (b s),
--     case inl {
--       apply exists.intro S,
--       apply exists.intro s,
--       exact small_step.ite_true h },
--     case inr {
--       apply exists.intro T,
--       apply exists.intro s,
--       exact small_step.ite_false h } },
--   case while : b S ih {
--     simp,
--     apply exists.intro (stmt.ite b (S ;; stmt.while b S) stmt.skip),
--     apply exists.intro s,
--     exact small_step.while }
-- end
end LoVe


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
