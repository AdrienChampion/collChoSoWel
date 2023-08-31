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