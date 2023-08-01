import Choice.Chapter1.Section1



/-! # Section 1.2 -/
namespace Choice



variable
  (R : Rel α)
  (a a' : α) [R.InDom a] [R.InDom a']

/-- `P`reference, decidable. -/
abbrev Rel.P :=
  R a a' ∧ ¬ R a' a

/-- `I`ndecisiveness, decidable. -/
abbrev Rel.I :=
  R a a' ∧ R a' a



/-- Nothing is more prefered. -/
@[simp]
abbrev Rel.max : Prop :=
  ∀ (a' : α), [InDom R a'] → ¬ R.P a' a

/-- `M`aximal set. -/
abbrev Rel.M : Set α :=
  R.max

/-- All are prefered. -/
@[simp]
abbrev Rel.best : Prop :=
  ∀ (a' : α), [InDom R a'] → R a a'

/-- `C`hoice set. -/
abbrev Rel.C : Set α :=
  R.best

theorem Rel.max_of_best
  (a : α)
: R.C a → R.M a :=
  fun h_best a' _ h_P_a'a =>
    h_P_a'a.right $ h_best a'