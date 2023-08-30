import Choice.Chapter2



namespace Choice



/-- A **s**ocial **w**elfare **f**unction. -/
abbrev Swf (α : Type u) :=
  Ccr (Order α) (Order α)


/-! ## Arrow's conditions -/
section conditions
  /-- `U`nrestricted `do`main.

  Lean functions are total, so `Udo` is actually already required by `Swf α`.
  -/
  @[simp]
  abbrev Swf.Udo (_ : Swf α count) : Prop :=
    True

  /-- `W`eak `p`areto `p`rinciple. -/
  abbrev Swf.Wpp (swf : Swf α count) : Prop :=
    ∀ (chs : Choices.Ordered α count),
    ∀ (x y : α),
      (∀ (i : chs.Idx), chs[i].lt x y)
      → (swf chs).lt x y

  /-- `I`ndependence of `i`rrelevant `a`lternatives. -/
  abbrev Swf.Iia
    (swf : Swf α count)
  : Prop :=
    ∀ (chs chs' : Choices.Ordered α count),
      ∀ (S : Set α),
        (∀ (x y : S), ∀ (i : chs.Idx),
          chs[i].le x y ↔ (chs'[i].le x y))
        → ((swf chs).sub S).C = ((swf chs').sub S).C

  /-- `N`on-`di`ctatorship. -/
  abbrev Swf.Ndi
    (swf : Swf α count)
  : Prop :=
    ∀ (chs : Choices.Ordered α count),
      ¬ ∃ (i : chs.Idx),
        (∀ (x y : α), chs[i].lt x y → (swf chs).lt x y)
    
  abbrev Swf.dictator
    (swf : Swf α count)
    (chs : Choices.Ordered α count)
    (i : chs.Idx)
  : Prop :=
    ∀ (x y : α), chs[i].lt x y → (swf chs).lt x y

  theorem Swf.not_Ndi_of_dictator
    (swf : Swf α count)
    (chs : Choices.Ordered α count)
    (i : chs.Idx)
  : swf.dictator chs i → ¬ swf.Ndi := by
    simp [dictator]
    intro dicta
    exists chs
    exists i
    intro x y nyx xy
    exact dicta x y xy nyx
end conditions



/-! ## Decisiveness -/
section decisive
  def Swf.almost_decisive
    (swf : Swf α count)
    (I : Set (Fin count))
    (x y : α)
  : Prop :=
    ∀ (chs : Choices.Ordered α count),
    (∀ (i : I), chs[i.1].lt x y)
    → (∀ (i : I.compl), chs[i.1].lt y x)
    → (swf chs).lt x y

  def Swf.decisive
    (swf : Swf α count)
    (I : Set (Fin count))
    (x y : α)
  : Prop :=
    ∀ (chs : Choices.Ordered α count),
    (∀ (i : I), chs[i.1].lt x y)
    → (swf chs).lt x y

  theorem Swf.almost_decisive_of_decisive
    {swf : Swf α count}
    {I : Set (Fin count)}
    {x y : α}
  : swf.decisive I x y → swf.almost_decisive I x y := by
    intro dec
    intro chs h _
    exact dec chs h


  -- abbrev Swf.almost_dec
  --   (swf : Swf α)
  --   (chs : Choices.Ordered α)
  --   (i : chs.Idx)
  --   (x y : α)
  -- : Prop :=
  --   swf.almost_decisive chs {i} x y

  -- def Swf.dec
  --   (swf : Swf α)
  --   (chs : Choices.Ordered α)
  --   (i : chs.Idx)
  --   (x y : α)
  -- : Prop :=
  --   swf.decisive chs {i} x y

  -- theorem Swf.almost_dec_of_dec
  --   (swf : Swf α)
  --   (chs : Choices.Ordered α)
  --   (i : chs.Idx)
  --   (x y : α)
  -- : swf.dec chs i x y → swf.almost_dec chs i x y :=
  --   swf.almost_decisive_of_decisive chs {i} x y
end decisive



-- theorem Swf.iia_almost_dec
--   (swf : Swf α)
--   (chs chs' : Choices.Ordered α)
--   (J : chs.Idx)
--   (x y : α)
--   (iia : swf.Iia)
--   (aldec : swf.almost_dec chs J x y)
--   (h_count : chs.count = chs'.count)
--   (h_xy : ∀ (i : chs.Idx), chs[i].le x y ↔ (chs'.get ⟨i.1, h_count ▸ i.2⟩).le x y)
--   (h_yx : ∀ (i : chs.Idx), chs[i].le y x ↔ (chs'.get ⟨i.1, h_count ▸ i.2⟩).le y x)
-- : swf.almost_dec chs' ⟨J.1, h_count ▸ J.2⟩ x y := by
--   let C_eq_C' := iia chs chs' h_count {x, y}
--     (by
--       intro a b i
--       let h_a := a.2
--       simp at h_a
--       let h_b := b.2
--       simp at h_b
--       cases h_a with
--       | inl h_ax =>
--         cases h_b with
--         | inl h_bx =>
--           rw [h_ax, h_bx]
--           simp [Preorder.le_refl]
--         | inr h_by =>
--           rw [h_ax, h_by]
--           exact h_xy i
--       | inr h_ay =>
--         cases h_b with
--         | inl h_bx =>
--           rw [h_ay, h_bx]
--           exact h_yx i
--         | inr h_by =>
--           rw [h_ay, h_by]
--           simp [Preorder.le_refl])
--   simp [almost_dec, almost_decisive]
--   intro x_le'_y not_y_le'_x h'_not_J
--   let x_le_y := (h_xy J).mpr x_le'_y
--   let not_y_le_x := (h_yx J).not.mpr not_y_le'_x
--   let h_not_J : ∀ (i : chs.Idx), i ∈ Set.compl {J} → chs[i].le y x ∧ ¬ chs[i].le x y := by
--     intro i i_in_compl
--     simp [almost_dec, almost_decisive, ProtoOrder.lt_def] at aldec
--     let y_lt'_x := h'_not_J ⟨i.1, h_count ▸ i.2⟩
--       (by
--         intro h
--         let i_eq_J := Set.mem_singleton_iff.mp h
--         simp at i_eq_J
--         apply i_in_compl
--         apply Set.mem_singleton_iff.mpr
--         rw [Fin.mk_eq_mk]
--         exact i_eq_J)
--     exact ⟨(h_yx i).mpr y_lt'_x.left, (h_xy i).not.mpr y_lt'_x.right⟩
--   simp [almost_dec, almost_decisive] at aldec
--   let x_lt_y := aldec x_le_y not_y_le_x h_not_J
--   let S : Set α := {x, y}
--   let x_in_S : x ∈ S := Set.mem_insert x {y}
--   let y_in_S : y ∈ S := Set.mem_insert_iff.mpr (Or.inr $ Set.mem_singleton y)
--   let x_in_C : ⟨x, x_in_S⟩ ∈ (swf chs |>.sub {x, y}).C := by
--     rw [ProtoOrder.C_def]
--     intro b
--     cases b with | mk b b_in_S =>
--     let h := Set.mem_insert_iff.mp b_in_S
--     cases h with
--     | inl h_bx =>
--       simp [LE.le]
--       rw [h_bx]
--       apply Preorder.le_refl
--     | inr h_by =>
--       simp [LE.le]
--       rw [h_by]
--       exact x_lt_y.left
--   let y_notin_C : ⟨y, y_in_S⟩ ∉ (swf chs |>.sub {x, y}).C := by
--     rw [ProtoOrder.C_def]
--     intro b
--     simp [LE.le] at b
--     exact x_lt_y.right b.left
--   let x_in_C := C_eq_C' ▸ x_in_C
--   let y_notin_C := C_eq_C' ▸ y_notin_C
--   simp [ProtoOrder.C_def] at x_in_C y_notin_C
--   constructor
--   · let tmp := x_in_C y
--     simp [LE.le] at tmp
--     exact tmp
--   · let ⟨cex, ⟨dom, not_y_cex⟩⟩ := y_notin_C
--     simp [LE.le] at not_y_cex
--     cases dom with
--     | inl h_cex_x =>
--       rw [h_cex_x] at not_y_cex
--       assumption
--     | inr h_cex_y =>
--       rw [h_cex_y] at not_y_cex
--       intro
--       apply not_y_cex
--       apply Preorder.le_refl



-- theorem Swf.iia_dec
--   (swf : Swf α)
--   (chs chs' : Choices.Ordered α)
--   (J : chs.Idx)
--   (x y : α)
--   (iia : swf.Iia)
--   (aldec : swf.dec chs J x y)
--   (h_count : chs.count = chs'.count)
--   (h_xy : ∀ (i : chs.Idx), chs[i].le x y ↔ (chs'.get ⟨i.1, h_count ▸ i.2⟩).le x y)
--   (h_yx : ∀ (i : chs.Idx), chs[i].le y x ↔ (chs'.get ⟨i.1, h_count ▸ i.2⟩).le y x)
-- : swf.dec chs' ⟨J.1, h_count ▸ J.2⟩ x y := by
--   let C_eq_C' := iia chs chs' h_count {x, y}
--     (by
--       intro a b i
--       let h_a := a.2
--       simp at h_a
--       let h_b := b.2
--       simp at h_b
--       cases h_a with
--       | inl h_ax =>
--         cases h_b with
--         | inl h_bx =>
--           rw [h_ax, h_bx]
--           simp [Preorder.le_refl]
--         | inr h_by =>
--           rw [h_ax, h_by]
--           exact h_xy i
--       | inr h_ay =>
--         cases h_b with
--         | inl h_bx =>
--           rw [h_ay, h_bx]
--           exact h_yx i
--         | inr h_by =>
--           rw [h_ay, h_by]
--           simp [Preorder.le_refl])
--   simp [dec, decisive]
--   intro x_le'_y not_y_le'_x
--   let x_le_y := (h_xy J).mpr x_le'_y
--   let not_y_le_x := (h_yx J).not.mpr not_y_le'_x
--   simp [dec, decisive] at aldec
--   let x_lt_y := aldec x_le_y not_y_le_x
--   let S : Set α := {x, y}
--   let x_in_S : x ∈ S := Set.mem_insert x {y}
--   let y_in_S : y ∈ S := Set.mem_insert_iff.mpr (Or.inr $ Set.mem_singleton y)
--   let x_in_C : ⟨x, x_in_S⟩ ∈ (swf chs |>.sub {x, y}).C := by
--     rw [ProtoOrder.C_def]
--     intro b
--     cases b with | mk b b_in_S =>
--     let h := Set.mem_insert_iff.mp b_in_S
--     cases h with
--     | inl h_bx =>
--       simp [LE.le]
--       rw [h_bx]
--       apply Preorder.le_refl
--     | inr h_by =>
--       simp [LE.le]
--       rw [h_by]
--       exact x_lt_y.left
--   let y_notin_C : ⟨y, y_in_S⟩ ∉ (swf chs |>.sub {x, y}).C := by
--     rw [ProtoOrder.C_def]
--     intro b
--     simp [LE.le] at b
--     exact x_lt_y.right b.left
--   let x_in_C := C_eq_C' ▸ x_in_C
--   let y_notin_C := C_eq_C' ▸ y_notin_C
--   simp [ProtoOrder.C_def] at x_in_C y_notin_C
--   constructor
--   · let tmp := x_in_C y
--     simp [LE.le] at tmp
--     exact tmp
--   · let ⟨cex, ⟨dom, not_y_cex⟩⟩ := y_notin_C
--     simp [LE.le] at not_y_cex
--     cases dom with
--     | inl h_cex_x =>
--       rw [h_cex_x] at not_y_cex
--       assumption
--     | inr h_cex_y =>
--       rw [h_cex_y] at not_y_cex
--       intro
--       apply not_y_cex
--       apply Preorder.le_refl
