import Choice.Chapter2.Section1



namespace Choice



section kaldor
  abbrev ProtoOrder.above
    [_P : ProtoOrder α]
    (x : α)
  : Set α :=
    fun y => y = x ∨ x ≤ y

  instance [P : ProtoOrder α] (x : α) : ∀ a, Decidable (a ∈ P.above x) := fun a => by
    simp [ProtoOrder.above, Set.mem_def]
    exact inferInstance
  
  protected abbrev Kaldor.lt
    (P : ProtoOrder α)
    (chs : Choices.Ordered α)
    (x y : α)
  : Prop :=
    ∃ (z : P.above x),
      (∀ (i : chs.Idx), chs[i].le z y)
      ∧ ∃ (i : chs.Idx), chs[i].lt z y

  abbrev Kaldor
    (P : ProtoOrder α)
    (chs : Choices.Ordered α)
  : Prop :=
    ∀ (x y : α),
      x < y ↔ Kaldor.lt P chs x y
  
  /-- An actual CEX would be better as inputs might be unsat. -/
  theorem Kaldor.inconsistent
    (P : ProtoOrder α)
    (chs : Choices.Ordered α)
    [Inhabited chs.Idx]
    (x y z w : α)
    (z_above_x : z ∈ P.above x)
    (w_above_y : w ∈ P.above y)
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
      apply And.intro (pareto_zy _) pareto_nyz
    · rw [kaldor]
      exists ⟨w, w_above_y⟩
      apply And.intro pareto_wx
      exists pareto_nxw_i
      apply And.intro (pareto_wx _) pareto_nxw
end kaldor



section scitovsky
  protected abbrev Scitovsky.lt
    (P : ProtoOrder α)
    (chs : Choices.Ordered α)
    (x y : α)
  : Prop :=
    Kaldor.lt P chs x y ∧ ¬ Kaldor.lt P chs y x

  abbrev Scitovsky
    (P : ProtoOrder α)
    (chs : Choices.Ordered α)
  : Prop :=
    ∀ (x y : α), x < y ↔ Scitovsky.lt P chs x y

  /-- An actual CEX would be better as inputs might be unsat. -/
  theorem Scitovsky.inconsistent
    (P : ProtoOrder α)
    (chs : Choices.Ordered α)
    (x y z x' y' : α)
    (x'_above_x : x' ∈ P.above x)
    (y'_above_y : y' ∈ P.above y)
    (x'_lt_y : Pareto.lt α chs x' y)
    (y'_lt_z : Pareto.lt α chs y' z)
    (hx : ¬ ∃ (y' : P.above y), Pareto.lt α chs y' x)
    (hy : ¬ ∃ (z' : P.above z), Pareto.lt α chs z' y)
    (hz : ¬ ∃ (x' : P.above x), Pareto.lt α chs x' z)
  : ¬ Transitive (Scitovsky.lt P chs) := by
    simp at x'_lt_y y'_lt_z hx hy hz
    intro h_trans
    let h₁ : Scitovsky.lt P chs x y := by
      constructor
      · simp
        exists x'
        constructor
        · exact x'_lt_y.left
        · apply And.intro x'_above_x
          simp [Pareto.lt] at x'_lt_y
          let ⟨i, nyx'⟩ := x'_lt_y.right
          exists i
          exact ⟨x'_lt_y.left i, nyx'⟩
      · simp
        intro a h a_above_y i _
        exact hx a h a_above_y i
    let h₂ : Scitovsky.lt P chs y z := by
      constructor
      · simp
        exists y'
        constructor
        · exact y'_lt_z.left
        · apply And.intro y'_above_y
          simp [Pareto.lt] at y'_lt_z
          let ⟨i, nzy'⟩ := y'_lt_z.right
          exists i
          exact ⟨y'_lt_z.left i, nzy'⟩
      · simp
        intro a h a_above_y i _
        exact hy a h a_above_y i
    let h₃ : ¬ Scitovsky.lt P chs x z := by
      simp only [Scitovsky.lt]
      intro h
      cases h with | intro x_lt_z not_z_lt_x =>
      simp [Kaldor.lt] at x_lt_z
      cases x_lt_z with | intro z' h =>
      cases h with | intro h₁ h₂ =>
      let hz := hz z' h₁ h₂.left
      let ⟨i, z'_lt_z⟩ := h₂.right
      exact z'_lt_z.right (hz i)
    apply h₃
    exact h_trans h₁ h₂



  abbrev Scitovsky.condition
    (P : ProtoOrder α)
    (chs : Choices.Ordered α)
  : Prop :=
    ∀ (x y : α),
      (∃ (x' : P.above x), Pareto.lt α chs x' y)
      → ∀ (y' : P.above y), ∃ (x' : P.above x), Pareto.le α chs x' y'

  -- theorem lemma_2_h
  --   (P : ProtoOrder α)
  --   (chs : Choices.Ordered α)
  -- : Scitovsky.condition P chs → Transitive (Scitovsky.lt P chs) := by
  --   simp [Scitovsky.lt, Scitovsky.condition, Kaldor.lt]
  --   intro h x y z x_lt_y y_lt_z
  --   let ⟨⟨x', x'y, x'_above_x, ex_x'_lt_y⟩, not_y_le_x⟩ := x_lt_y
  --   let ⟨⟨y', y'z, y'_above_y, ex_y'_lt_z⟩, not_z_le_y⟩ := y_lt_z
  --   let ⟨⟨x', h_x'⟩, not_y_le_x⟩ := x_lt_y
  --   let ⟨⟨y', h_y'⟩, not_z_le_y⟩ := y_lt_z
  --   constructor
  --   · exists y'
  --     exact h_y'
  --     sorry
  --   · sorry
  --   · sorry

end scitovsky

