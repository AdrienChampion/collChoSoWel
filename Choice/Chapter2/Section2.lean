import Choice.Chapter2.Section1



namespace Choice



section kaldor
  abbrev Choices.above
    (chs : Choices.Ordered α count)
    (x : α)
  : Set α :=
    fun y => Pareto.le α chs x y
  
  protected abbrev Kaldor.lt
    (chs : Choices.Ordered α count)
    (x y : α)
  : Prop :=
    ∃ (z : chs.above x),
      (∀ (i : chs.Idx), chs[i].le z y)
      ∧ ∃ (i : chs.Idx), ¬ chs[i].le y z

  abbrev Kaldor
    (_P : ProtoOrder α)
    (chs : Choices.Ordered α count)
  : Prop :=
    ∀ (x y : α),
      x < y ↔ Kaldor.lt chs x y
  
  /-- An actual CEX would be better as inputs might be unsat. -/
  theorem Kaldor.inconsistent
    (P : ProtoOrder α)
    (chs : Choices.Ordered α count)
    [Inhabited chs.Idx]
    (x y z w : α)
    (z_above_x : z ∈ chs.above x)
    (w_above_y : w ∈ chs.above y)
  : Pareto.lt α chs z y
  → Pareto.lt α chs w x
  → Kaldor P chs
  → False
  := by
    simp
    intro pareto_zy pareto_nyz_i pareto_nyz pareto_wx pareto_nxw_i pareto_nxw kaldor
    apply P.lt_asymm' x y
    · rw [kaldor]
      exists ⟨z, z_above_x⟩
      apply And.intro pareto_zy
      exists pareto_nyz_i
    · rw [kaldor]
      exists ⟨w, w_above_y⟩
      apply And.intro pareto_wx
      exists pareto_nxw_i
end kaldor



section scitovsky
  protected abbrev Scitovsky.lt
    (chs : Choices.Ordered α count)
    (x y : α)
  : Prop :=
    Kaldor.lt chs x y ∧ ¬ Kaldor.lt chs y x

  abbrev Scitovsky
    (_P : ProtoOrder α)
    (chs : Choices.Ordered α count)
  : Prop :=
    ∀ (x y : α), x < y ↔ Scitovsky.lt chs x y

  /-- An actual CEX would be better as inputs might be unsat. -/
  theorem Scitovsky.inconsistent
    (chs : Choices.Ordered α count)
    (x y z x' y' : α)
    (x'_above_x : x' ∈ chs.above x)
    (y'_above_y : y' ∈ chs.above y)
    (x'_lt_y : Pareto.lt α chs x' y)
    (y'_lt_z : Pareto.lt α chs y' z)
    (hx : ¬ ∃ (y' : chs.above y), Pareto.lt α chs y' x)
    (hy : ¬ ∃ (z' : chs.above z), Pareto.lt α chs z' y)
    (hz : ¬ ∃ (x' : chs.above x), Pareto.lt α chs x' z)
  : ¬ Transitive (Scitovsky.lt chs) := by
    simp at x'_lt_y y'_lt_z hx hy hz
    intro h_trans
    let h₁ : Scitovsky.lt chs x y := by
      constructor
      · simp
        exists x'
        constructor
        · exact x'_lt_y.left
        · apply And.intro x'_above_x
          simp [Pareto.lt] at x'_lt_y
          let ⟨i, nyx'⟩ := x'_lt_y.right
          exists i
      · simp
        intro a h a_above_y i
        exact hx a h a_above_y i
    let h₂ : Scitovsky.lt chs y z := by
      constructor
      · simp
        exists y'
        constructor
        · exact y'_lt_z.left
        · apply And.intro y'_above_y
          simp [Pareto.lt] at y'_lt_z
          let ⟨i, nzy'⟩ := y'_lt_z.right
          exists i
      · simp
        intro a h a_above_y i
        exact hy a h a_above_y i
    let h₃ : ¬ Scitovsky.lt chs x z := by
      simp only [Scitovsky.lt]
      intro h
      cases h with | intro x_lt_z not_z_lt_x =>
      simp [Kaldor.lt] at x_lt_z
      cases x_lt_z with | intro z' h =>
      cases h with | intro h₁ h₂ =>
      let hz := hz z' h₁ h₂.left
      let ⟨i, not_z_le_z'⟩ := h₂.right
      exact not_z_le_z' (hz i)
    apply h₃
    exact h_trans h₁ h₂



  abbrev Scitovsky.condition
    (chs : Choices.Ordered α count)
  : Prop :=
    ∀ (x y : α),
      (∃ (x' : chs.above x), Pareto.lt α chs x' y)
      → ∀ (y' : chs.above y), ∃ (x' : chs.above x), Pareto.le α chs x' y'

  theorem lemma_2_h
    (chs : Choices.Ordered α count)
    [Inhabited chs.Idx]
  : Scitovsky.condition chs → Transitive (Scitovsky.lt chs) := by
    intro h
    -- simp only [Scitovsky.lt, Kaldor.lt]
    intro x y z x_lt_y y_lt_z
    let ⟨⟨⟨x', x'_above_x⟩, ⟨all_x'y, one_not_y_le_x'⟩⟩, _not_y_lt_x⟩ := x_lt_y
    let ⟨⟨⟨y', y'_above_y⟩, ⟨all_y'z, one_not_z_le_y'⟩⟩, not_z_lt_y⟩ := y_lt_z
    clear x_lt_y y_lt_z
    let pareto_x'_lt_y : Pareto.lt α chs x' y :=
      by
        simp [Pareto.lt, Pareto.le]
        exact ⟨all_x'y, one_not_y_le_x'⟩
    constructor
    · simp only [Kaldor.lt]
      let ⟨⟨x'', x''_above_x⟩, h_x''⟩ :=
        h x y ⟨⟨x', x'_above_x⟩, pareto_x'_lt_y⟩ ⟨y', y'_above_y⟩
      exists ⟨x'', x''_above_x⟩
      constructor
      · intro i
        apply chs[i].le_trans (h_x'' i) (all_y'z i)
      · let ⟨i, nzy'⟩ := one_not_z_le_y'
        exists i
        intro zx''
        let zy' := chs[i].le_trans zx'' (h_x'' i)
        contradiction
    · intro h_z'
      simp only [Kaldor.lt] at h_z'
      let ⟨⟨z', z'_above_x⟩, all_z'x, one_not_x_le_z'⟩ := h_z'
      clear h_z'
      let pareto_z'_lt_x : Pareto.lt α chs z' x :=
        by
          simp [Pareto.lt, Pareto.le]
          exact ⟨all_z'x, one_not_x_le_z'⟩
      let ⟨⟨z'', z''_above_z⟩, z''x'⟩ :=
        h z x ⟨⟨z', z'_above_x⟩, pareto_z'_lt_x⟩ ⟨x', x'_above_x⟩
      apply not_z_lt_y
      simp only [Kaldor.lt]
      exists ⟨z'', z''_above_z⟩
      constructor
      · intro i
        exact chs[i].le_trans (z''x' i) (pareto_x'_lt_y.left i)
      · let ⟨i, nyx'⟩ := one_not_y_le_x'
        exists i
        intro yz''
        apply nyx'
        exact chs[i].le_trans yz'' (z''x' i)

end scitovsky

