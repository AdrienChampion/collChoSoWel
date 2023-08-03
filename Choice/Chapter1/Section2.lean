import Choice.Chapter1.Section1



/-! # Section 1.2 -/
namespace Choice



variable
  (R : Rel α)

/-- **Strict** `P`reference, decidable.

- not reflexive
- transitive if `R.Trans`
-/
def Rel.P : Rel α where
  Dom := R.Dom
  R a a' := R a a' ∧ ¬ R a' a
  decidable := inferInstance

def Rel.P_irrefl : ¬ R.P a a := by
  simp [P]

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
def Rel.I : Rel α where
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



section max
  /-- Nothing is more prefered. -/
  @[simp]
  abbrev Rel.max
    (a : α)
  : Prop :=
    InDom R a ∧ (∀ (a' : α) [R.InDom a'], ¬ R.P a' a)

  /-- `M`aximal set, see `Rel.max`. -/
  abbrev Rel.M : Set α :=
    R.max

  def Rel.isMaxOf
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
  : List α → Bool
  | [] => true
  | hd::tl =>
    if R.P hd a then false else R.isMaxOf a tl

  def Rel.not_isMax_to_cex
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
    (list : List α)
  : ¬ R.isMaxOf a list → ∃ (a' : α), a' ∈ list ∧ R.P a' a := by
    intro h_isMaxOf
    induction list with
    | nil =>
      contradiction
    | cons hd tail ih =>
      simp [isMaxOf] at h_isMaxOf
      cases Decidable.em (R.P hd a) with
      | inl h =>
        simp [h] at h_isMaxOf
        exists hd
        simp [h]
      | inr h =>
        simp [h] at h_isMaxOf
        let ⟨cex, ⟨h_cex_dom, h_P⟩⟩ := ih (by simp [h_isMaxOf])
        exists cex
        exact And.intro (List.Mem.tail hd h_cex_dom) h_P      

  theorem Rel.isMaxOf_max_mp
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
    (list : List α)
  : R.isMaxOf a list → ∀ (a' : α), a' ∈ list → ¬ R.P a' a := by
    intro h_isMaxOf a' a'_dom
    induction list with
    | nil =>
      contradiction
    | cons hd tl ih =>
      simp only [isMaxOf] at h_isMaxOf
      if h : R.P hd a
      then simp [h] at h_isMaxOf
      else
        simp only [] at h
        simp [h] at h_isMaxOf
        cases a'_dom
        · exact h
        case tail h_a'_dom =>
          exact ih h_isMaxOf h_a'_dom

  theorem Rel.isMaxOf_max_mpr
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
    (list : List α)
  : (∀ (a' : α), a' ∈ list → ¬ R.P a' a) → R.isMaxOf a list := by
    intro h_max
    cases list with
    | nil =>
      simp [isMaxOf]
    | cons head tail =>
      simp only [isMaxOf]
      simp [h_max head (List.mem_cons_self _ _)]
      apply R.isMaxOf_max_mpr a tail
      intro a' a'_dom
      exact h_max a' (List.Mem.tail _ a'_dom)

  theorem Rel.isMaxOf_iff_max
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
    (list : List α)
  : R.isMaxOf a list ↔ (∀ (a' : α), a' ∈ list → ¬ R.P a' a) :=
    ⟨R.isMaxOf_max_mp a list, R.isMaxOf_max_mpr a list⟩

  def Rel.isMax
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
  : Bool :=
    R.isMaxOf a R.listDom

  theorem Rel.isMax_iff_max
    {R : Rel α}
    [Set.Finite R.Dom]
    {a : α} [aInDom : R.InDom a]
  : R.isMax a ↔ a ∈ R.M := by
    constructor
    · intro h_isMax
      let h := (R.isMaxOf_iff_max a R.listDom).mp h_isMax
      simp only [Membership.mem, Set.mem, M, max]
      apply And.intro aInDom
      intro a' a'InDom
      apply h a' $ R.listDomIso.mpr a'InDom
    · intro h_M_a
      simp [Membership.mem, Set.mem, M, max] at h_M_a
      apply (R.isMaxOf_iff_max a R.listDom).mpr
      intro a' h_a'_dom
      let a'InDom := R.listDomIso.mp h_a'_dom
      exact h_M_a.right a'

  instance
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
  : Decidable (a ∈ R.M) :=
    if h : R.isMax a
    then
      Rel.isMax_iff_max.mp h
      |> isTrue
    else
      Rel.isMax_iff_max
      |> not_congr
      |>.mp h
      |> isFalse
end max



section best
  /-- Prefered to all. -/
  @[simp]
  abbrev Rel.best
    (a : α)
  : Prop :=
    InDom R a ∧ (∀ (a' : α) [InDom R a'], R a a')

  /-- `C`hoice set, see `Rel.best`. -/
  abbrev Rel.C : Set α :=
    R.best

  def Rel.isBestOf
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
  : List α → Bool
  | [] => true
  | hd::tl =>
    if R a hd then R.isBestOf a tl else false

  def Rel.not_isBest_to_cex
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
    (list : List α)
  : ¬ R.isBestOf a list → ∃ (a' : α), a' ∈ list ∧ ¬ R a a' := by
    intro h_isBestOf
    induction list with
    | nil =>
      contradiction
    | cons hd tail ih =>
      simp [isBestOf] at h_isBestOf
      cases Decidable.em (R a hd) with
      | inr h =>
        simp [h] at h_isBestOf
        exists hd
        simp [h]
      | inl h =>
        simp [h] at h_isBestOf
        let ⟨cex, ⟨h_cex_dom, h_R⟩⟩ := ih (by simp [h_isBestOf])
        exists cex
        exact And.intro (List.Mem.tail hd h_cex_dom) h_R

  theorem Rel.isBestOf_best_mp
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

  theorem Rel.isBestOf_best_mpr
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
    (list : List α)
  : (∀ (a' : α), a' ∈ list → R a a') → R.isBestOf a list := by
    intro h_best
    cases list with
    | nil =>
      simp [isBestOf]
    | cons head tail =>
      simp only [isBestOf]
      simp [h_best head (List.mem_cons_self _ _)]
      apply R.isBestOf_best_mpr a tail
      intro a' a'_dom
      exact h_best a' (List.Mem.tail _ a'_dom)

  theorem Rel.isBestOf_iff_best
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
    (list : List α)
  : R.isBestOf a list ↔ (∀ (a' : α), a' ∈ list → R a a') :=
    ⟨R.isBestOf_best_mp a list, R.isBestOf_best_mpr a list⟩

  def Rel.isBest
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
  : Bool :=
    R.isBestOf a R.listDom

  theorem Rel.isBest_iff_best
    {R : Rel α}
    [I : Set.Finite R.Dom]
    {a : α} [aInDom : R.InDom a]
  : R.isBest a ↔ a ∈ R.C := by
    simp [Membership.mem]
    constructor
    · intro h_isBest
      let h := (R.isBestOf_iff_best a R.listDom).mp h_isBest
      simp [best]
      apply And.intro aInDom
      intro a' a'InDom
      apply h a' $ I.iso.mpr a'InDom.inDom
    · intro h_C_a
      apply (R.isBestOf_iff_best a R.listDom).mpr
      intro a' h_a'_dom
      let a'InDom := R.listDomIso.mp h_a'_dom
      exact h_C_a.right a'

  instance
    (R : Rel α)
    [Set.Finite R.Dom]
    (a : α) [R.InDom a]
  : Decidable (a ∈ R.C) :=
    if h : R.isBest a
    then
      Rel.isBest_iff_best.mp h
      |> isTrue
    else
      Rel.isBest_iff_best
      |> not_congr
      |>.mp h
      |> isFalse
end best



/-- Best implies max, but not the other way around. -/
theorem Rel.max_of_best
  (a : α)
: a ∈ R.C → a ∈ R.M := by
  simp [Membership.mem]
  intro aInDom h_best
  apply And.intro aInDom
  intro a' _ h_a'_P_a
  exact h_a'_P_a.right $ h_best a'
