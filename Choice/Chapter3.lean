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
  abbrev Swf.Udo (_ : Swf α) : Prop :=
    True

  /-- `W`eak `p`areto `p`rinciple. -/
  abbrev Swf.Wpp (swf : Swf α) : Prop :=
    ∀ (chs : Choices.Ordered α),
    ∀ (x y : α),
      (∀ (i : chs.Idx), chs[i].le x y)
      → (swf chs).le x y

  /-- `I`ndependence of `i`rrelevant `a`lternatives. -/
  abbrev Swf.Iia
    (swf : Swf α)
  : Prop :=
    ∀ (chs chs' : Choices.Ordered α),
      (h : chs.count = chs'.count) →
      ∀ (S : Set α), ∀ (x y : S),
        (∀ (i : chs.Idx), chs[i].le x y ↔ (chs'.get ⟨i.1, h ▸ i.2⟩).le x y)
        → ((swf chs).sub S).C = ((swf chs').sub S).C
  
  /-- `N`on-`di`ctatorship. -/
  abbrev Swf.Ndi
    (swf : Swf α)
  : Prop :=
    ∀ (chs : Choices.Ordered α),
      ¬ ∃ (i : chs.Idx),
        (∀ (x y : α), chs[i].lt x y → (swf chs).lt x y)
    
  abbrev Swf.dictator
    (swf : Swf α)
    (chs : Choices.Ordered α)
    (i : chs.Idx)
  : Prop :=
    ∀ (x y : α), chs[i].lt x y → (swf chs).lt x y

  theorem Swf.not_Ndi_of_dictator
    (swf : Swf α)
    (chs : Choices.Ordered α)
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
    (swf : Swf α)
    (chs : Choices.Ordered α)
    (I : Set chs.Idx)
    (x y : α)
  : Prop :=
    (∀ (i : I), chs[i.1].lt x y)
    → (∀ (i : I.compl), chs[i.1].lt y x)
    → (swf chs).lt x y

  def Swf.decisive
    (swf : Swf α)
    (chs : Choices.Ordered α)
    (I : Set chs.Idx)
    (x y : α)
  : Prop :=
    (∀ (i : I), chs[i.1].lt x y)
    → (swf chs).lt x y

  theorem Swf.almost_decisive_of_decisive
    (swf : Swf α)
    (chs : Choices.Ordered α)
    (I : Set chs.Idx)
    (x y : α)
  : swf.decisive chs I x y → swf.almost_decisive chs I x y := by
    intro dec
    intro h _
    exact dec h


  abbrev Swf.almost_dec
    (swf : Swf α)
    (chs : Choices.Ordered α)
    (i : chs.Idx)
    (x y : α)
  : Prop :=
    swf.almost_decisive chs {i} x y

  def Swf.dec
    (swf : Swf α)
    (chs : Choices.Ordered α)
    (i : chs.Idx)
    (x y : α)
  : Prop :=
    swf.decisive chs {i} x y

  theorem Swf.almost_dec_of_dec
    (swf : Swf α)
    (chs : Choices.Ordered α)
    (i : chs.Idx)
    (x y : α)
  : swf.dec chs i x y → swf.almost_dec chs i x y :=
    swf.almost_decisive_of_decisive chs {i} x y
end decisive



theorem lemma_3_a
  (swf : Swf α)
  (chs : Choices.Ordered α)
  (i : chs.Idx)
  (x y : α)
: swf.almost_dec chs i x y
  → swf.Udo
  → swf.Wpp
  → swf.Iia
  → swf.dictator chs i
:= by
  sorry

theorem lemma_3_a'
  (swf : Swf α)
  (chs : Choices.Ordered α)
  (i : chs.Idx)
  (x y : α)
: swf.almost_dec chs i x y
  → swf.Udo
  → swf.Wpp
  → swf.Iia
  → ¬ swf.Ndi
:= by
  intro h udo wpp iia
  apply swf.not_Ndi_of_dictator chs i
  exact lemma_3_a swf chs i x y h udo wpp iia



theorem Swf.arrow
  (swf : Swf α)
: ¬ (swf.Udo ∧ swf.Wpp ∧ swf.Iia ∧ swf.Ndi) := by
  sorry
