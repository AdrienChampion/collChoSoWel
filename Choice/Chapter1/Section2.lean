import Choice.Chapter1.Section1



/-! # Section 1.2 -/
namespace Choice



variable
  (R : Rel α)

/-- **Strict** `P`reference, decidable.

- not reflexive
- transitive if `R.Trans`
-/
abbrev Rel.P : Rel α where
  Dom := R.Dom
  R a a' := R a a' ∧ ¬ R a' a
  decidable := inferInstance

theorem Rel.P_Dom : R.Dom = R.P.Dom :=
  rfl
instance [I : R.P.InDom a] : R.InDom a where
  inDom := I.inDom
instance [I : R.InDom a] : R.P.InDom a where
  inDom := I.inDom

instance [instTrans : R.Trans] : R.P.Trans where
  trans
    {a a' a'' : α} [R.P.InDom a] [R.P.InDom a'] [R.P.InDom a'']
    (h₁ : R.P a a')
    (h₂ : R.P a' a'')
  := ⟨
    instTrans.trans h₁.left h₂.left,
    fun h_a''a =>
      let h_a'a := instTrans.trans h₂.left h_a''a
      h₁.right h_a'a
  ⟩



/-- `I`ndecisiveness, decidable.

- reflexive if `R.Refl`
- transitive if `R.Trans`
-/
abbrev Rel.I : Rel α where
  Dom := R.Dom
  R a a' := R a a' ∧ R a' a
  decidable := inferInstance

theorem Rel.I_Dom : R.Dom = R.I.Dom :=
  rfl
instance [I : R.I.InDom a] : R.InDom a where
  inDom := I.inDom
instance [I : R.InDom a] : R.I.InDom a where
  inDom := I.inDom

instance [instRefl : R.Refl] : R.I.Refl where
  refl {a : α} [R.I.InDom a] := ⟨
    instRefl.refl,
    instRefl.refl
  ⟩

instance [instTrans : R.Trans] : R.I.Trans where
  trans
    {a a' a'' : α} [R.I.InDom a] [R.I.InDom a'] [R.I.InDom a'']
    (h₁ : R.I a a')
    (h₂ : R.I a' a'')
  := ⟨
    instTrans.trans h₁.left h₂.left,
    instTrans.trans h₂.right h₁.right
  ⟩



variable
  (a a' : α) [R.InDom a] [R.InDom a']



/-- Nothing is more prefered. -/
@[simp]
abbrev Rel.max : Prop :=
  ∀ (a' : α), [InDom R a'] → ¬ R.P a' a

/-- `M`aximal set, see `Rel.max`. -/
abbrev Rel.M : Set α :=
  R.max

/-- All are prefered. -/
@[simp]
abbrev Rel.best : Prop :=
  ∀ (a' : α), [InDom R a'] → R a a'

/-- `C`hoice set, see `Rel.best`. -/
abbrev Rel.C : Set α :=
  R.best

/-- Best implies max, but not the other way around. -/
theorem Rel.max_of_best
  (a : α)
: R.C a → R.M a :=
  fun h_best a' _ h_P_a'a =>
    h_P_a'a.right $ h_best a'