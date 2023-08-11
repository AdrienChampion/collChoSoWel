import Choice.Chapter1.Section2



/-! # Section 1.3 -/
namespace Choice



/-! ### Lemma `1*a` -/
namespace lemma_1_a
  variable
    [R : Preorder α]
    {x y z : α}

  theorem trans_I : x ≈ y → y ≈ z → x ≈ z :=
    Trans.trans

  theorem trans_PI : x < y → y ≈ z → x < z :=
    fun xy yz => by
      simp [R.lt_def, R.equiv_def] at *
      apply And.intro (Trans.trans xy.left yz.left)
      intro zx
      exact xy.right (Trans.trans yz.left zx)

  theorem trans_IP : x ≈ y → y < z → x < z :=
    fun xy yz => by
      simp [R.lt_def, R.equiv_def] at *
      apply And.intro (Trans.trans xy.left yz.left)
      intro zx
      exact yz.right (Trans.trans zx xy.left)
  
  theorem trans_P : x < y → y < z → x < z :=
    Trans.trans
end lemma_1_a



/-! ### Lemma `1*b` -/
section lemma_1_b
  /- Lemma 1.b.
  
  Original formulation omits the necessary assumption `Inhabited α`. -/
  theorem lemma_1_b
    (α : Type u)
    [R : Preorder α]
    [_F : Finite α]
    [_I : Inhabited α]
  : ∃ max, max ∈ R.M :=
    ⟨R.getMax, R.getMax_in_M rfl⟩

  abbrev Preorder.lemma_1_b
    [Preorder α]
    [Finite α]
    [Inhabited α]
  := Choice.lemma_1_b α
end lemma_1_b



section lemma_1_c
  theorem lemma_1_c'
    [R : Preorder α]
    [_F : Finite α]
    {a b : α}
    (h_ne : a ≠ b)
    (h_only : ∀ (x : α), x = a ∨ x = b)
  : a < b ↔ (∀ c, c ∈ R.C ↔ c = a) := ⟨
    by
      intro a_lt_b c
      constructor
      · intro C_c
        let h := h_only c
        cases h with
        | inl h =>
          assumption
        | inr h =>
          rw [← h] at a_lt_b
          let tmp := C_c a
          simp [R.lt_def] at a_lt_b
          let absurd := a_lt_b.right tmp
          contradiction
      · intro h
        rw [h]
        intro d
        cases h_only d with
        | inl h =>
          rw [h]
        | inr h =>
          rw [h]
          simp [R.lt_def] at a_lt_b
          exact a_lt_b.left
    ,
    by
      intro h
      simp [R.lt_def]
      apply And.intro
      · exact h a |>.mpr rfl b
      · intro b_le_a
        let C_b : b ∈ R.C := by
          intro c
          cases h_only c with
          | inl h =>
            rw [h]
            exact b_le_a
          | inr h =>
            rw [h]
        apply h_ne
        apply Eq.symm
        apply h b |>.mp C_b
  ⟩

  /-- Lemma 1.c.

  Assumption `h_ne` is not in the book, but it is necessary for the theorem's `Iff.mpr`, since `R.P`
  is not reflexive. The book version uses `[x, y]` for the set composed of `x` and `y`, which maybe
  indicates that `x` and `y` should be different 🤷‍♀️. -/
  theorem lemma_1_c
    [R : Preorder α]
    [_F : Finite α]
    {a b : α}
    (h_ne : a ≠ b)
    (h_only : ∀ (x : α), x = a ∨ x = b)
  : a < b ↔ R.C = {a} := by
    constructor
    · intro h
      apply Set.ext
      simp [Set.mem_singleton_of_eq]
      apply (lemma_1_c' h_ne h_only).mp h
    · intro h
      apply (lemma_1_c' h_ne h_only).mpr
      simp [h]
end lemma_1_c



section lemma_1_d
  /-- Lemma 1.d. -/
  theorem lemma_1_d
    [R : Preorder α]
    {best : α}
    (C_best : best ∈ R.C)
  : R.C = R.M :=
    Set.eq_of_subset_of_subset R.best_is_max (
      by
        intro max M_max a
        let best_le_a := C_best a
        let best_le_max := C_best max
        simp [R.M_def] at M_max
        let tmp := M_max best
        simp [R.lt_def] at tmp
        let max_le_best := tmp best_le_max
        apply Trans.trans max_le_best best_le_a
    )
end lemma_1_d



section lemma_1_e
  theorem lemma_1_e_mp
    [R : Preorder α] [F : Finite α] [I : Inhabited α]
  : (∀ (a b : α), a ∈ R.M → b ∈ R.M → a ≈ b) → (R.C = R.M) := by
    intro h
    let ⟨max, M_max⟩ := R.lemma_1_b
    let h_max b := h max b M_max
    apply lemma_1_d (best := max)
    intro a

    if h_a_max : a ∈ R.M then
      let max_eqv_a := h_max a h_a_max
      simp only [R.equiv_def] at max_eqv_a
      exact max_eqv_a.left
    else
      let ⟨maxₐ, maxₐ_lt_a, M_maxₐ⟩ :=
        R.max_of_not_max a h_a_max
      let maxₐ_eqv_a := h_max maxₐ M_maxₐ
      simp only [R.equiv_def] at maxₐ_eqv_a
      simp only [R.lt_def] at maxₐ_lt_a
      apply Trans.trans maxₐ_eqv_a.left maxₐ_lt_a.left

  theorem lemma_1_e_mpr
    [R : Preorder α] [_F : Finite α] [_I : Inhabited α]
  : (R.C = R.M) → (∀ (a b : α), a ∈ R.M → b ∈ R.M → a ≈ b) := by
    intro h a b M_a M_b
    let C_a : a ∈ R.C := by rw [h] ; assumption
    let C_b : b ∈ R.C := by rw [h] ; assumption
    simp [R.equiv_def]
    apply And.intro (C_a b) (C_b a)

  theorem lemma_1_e
    [R : Preorder α] [Finite α] [Inhabited α]
  : (∀ (a b : α), a ∈ R.M → b ∈ R.M → a ≈ b) ↔ (R.C = R.M) :=
    ⟨lemma_1_e_mp, lemma_1_e_mpr⟩
end lemma_1_e
