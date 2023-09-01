import Choice.Chapter2



namespace Choice



/-- A **s**ocial **w**elfare **f**unction. -/
abbrev Swf (α : Type u) :=
  Ccr (Order α) (Order α)




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

  theorem Swf.almost_decisive_refl
    {swf : Swf α count}
    {I : Set (Fin count)}
    [Inhabited I]
    {x : α}
  : swf.almost_decisive I x x := by
    intro chs wrong
    simp at wrong
    exfalso
    let ⟨i, h_i⟩ : I := default
    apply wrong i h_i

  theorem Swf.decisive_refl
    {swf : Swf α count}
    {I : Set (Fin count)}
    [Inhabited I]
    {x : α}
  : swf.decisive I x x := by
    intro chs wrong
    simp at wrong
    exfalso
    let ⟨i, h_i⟩ : I := default
    apply wrong i h_i
end decisive



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
  
  theorem Swf.iia_lt
    (swf : Swf α count)
    (iia : swf.Iia)
    (chs chs' : Choices.Ordered α count)
    (h : ∀ (i : Fin count),
      (chs[i].le x y ↔ chs'[i].le x y)
      ∧ (chs[i].le y x ↔ chs'[i].le y x))
  : (swf chs).lt x y → (swf chs').lt x y := by
    intro chs_x_lt_y
    let S : Set α :=
      {x, y}
    let x_in_S : x ∈ S :=
      Set.mem_insert x {y}
    let y_in_S : y ∈ S :=
      Set.mem_insert_iff.mp (Or.inr $ Set.mem_singleton y)
    let C_eq_C' :=
      iia chs chs' S
        (by
          simp [Preorder.le_refl]
          exact ⟨fun i => h i |>.left, fun i => h i |>.right⟩)

    let sub := (swf chs).sub S
    let _ := (swf chs).toLE

    let x_in_C : ⟨x, x_in_S⟩ ∈ sub.C := by
      rw [sub |>.C_def]
      simp [Preorder.le_refl]
      exact chs_x_lt_y.left
    let y_notin_C : ⟨y, y_in_S⟩ ∉ sub.C := by
      rw [sub |>.C_def]
      simp [Preorder.le_refl]
      exact chs_x_lt_y.right
    let x_in_C' := C_eq_C' ▸ x_in_C
    let y_notin_C' := C_eq_C' ▸ y_notin_C

    constructor
    · exact x_in_C' ⟨y, y_in_S⟩
    · intro y_le_x
      let sub' := (swf chs').sub S
      let _ := (swf chs').toLE
      apply y_notin_C'
      rw [sub'.C_def]
      simp [Preorder.le_refl]
      exact y_le_x

  /-- `N`on-`di`ctatorship. -/
  abbrev Swf.Ndi
    (swf : Swf α count)
  : Prop :=
    ¬ ∃ (i : Fin count), ∀ (x y : α), swf.decisive {i} x y
    
  abbrev Swf.dictator
    (swf : Swf α count)
    (i : Fin count)
  : Prop :=
    ∀ (x y : α), swf.decisive {i} x y
  
  abbrev Swf.partialDictator
    (swf : Swf α count)
    (i : Fin count)
    (S : Set α)
  : Prop :=
    ∀ (x y : S), swf.decisive {i} x y

  theorem Swf.not_Ndi_of_dictator
    (swf : Swf α count)
    (i : Fin count)
  : swf.dictator i → ¬ swf.Ndi := by
    simp [dictator]
    intro dicta
    exists i
end conditions