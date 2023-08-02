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



/-- `I`ndifference, decidable.

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
abbrev Rel.max
  (a : α) [I : R.InDom a]
: Prop :=
  let _ := I
  ∀ (a' : α), [InDom R a'] → ¬ R.P a' a

/-- `M`aximal set, see `Rel.max`. -/
abbrev Rel.M
  (a : α) [R.InDom a]
: Prop :=
  R.max a

/-- Prefered to all. -/
@[simp]
abbrev Rel.best
  (a : α) [R.InDom a]
: Prop :=
  ∀ (a' : α), [InDom R a'] → R a a'

def Rel.isBestOf
  (R : Rel α)
  [Set.Finite R.Dom]
  (a : α) [R.InDom a]
: List α → Bool
| [] => true
| hd::tl =>
  if R a hd then R.isBestOf a tl else false

theorem Rel.isBestOf_best
  (R : Rel α)
  [Set.Finite R.Dom]
  (a : α) [R.InDom a]
  (list : List α)
: R.isBestOf a list → ∀ (a' : α), a' ∈ list → R a a' := by
  induction list with
  | nil =>
    intro _ _ _
    contradiction
  | cons hd tl ih =>
    intro h_isBestOf a' a'_dom
    revert h_isBestOf
    simp [isBestOf]
    if h : R a hd
    then
      simp [h]
      intro h_isBestOf
      let h_sub_max := ih h_isBestOf
      cases a'_dom ; exact h
      case tail a'_dom =>
        exact h_sub_max a' a'_dom
    else simp [h]

def Rel.isBest
  (R : Rel α)
  [Set.Finite R.Dom]
  (a : α) [R.InDom a]
: Bool :=
  R.isBestOf a R.listDom

theorem Rel.isBest_best
  (R : Rel α)
  [I : Set.Finite R.Dom]
  (a : α) [R.InDom a]
: R.isBest a → R.best a := by
  intro h_isBest
  let h := R.isBestOf_best a R.listDom h_isBest
  simp [best]
  intro a' a'InDom
  apply h a' $ I.iso.mpr a'InDom.inDom



/-- `C`hoice set, see `Rel.best`. -/
abbrev Rel.C
  (a : α) [R.InDom a]
: Prop :=
  R.best a

/-- Best implies max, but not the other way around. -/
theorem Rel.max_of_best
  (a : α) [R.InDom a]
: R.C a → R.M a :=
  fun h_best a' _ h_P_a'a =>
    h_P_a'a.right $ h_best a'