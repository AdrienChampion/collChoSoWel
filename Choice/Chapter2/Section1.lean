import Choice.Chapter1.Section4



namespace Choice



/-! ## Aggregating individual choices -/

structure Choices (O : Type u) (count : ℕ) where
  choices : Array O
  inv : count = choices.size

@[simp]
protected abbrev Choices.count (_ : Choices O count) :=
  count



@[simp]
protected abbrev Choices.ProtoOrdered (α : Type u) :=
  Choices (ProtoOrder α)

@[simp]
protected abbrev Choices.PreOrdered (α : Type u) :=
  Choices (ProtoOrder α)

@[simp]
protected abbrev Choices.Ordered (α : Type u) :=
  Choices (Order α)



section
  variable
    {O : Type u}
    (chs : Choices O count)

  abbrev Choices.Idx (_ : Choices O count) :=
    Fin count

  def Choices.invariant :=
    chs.inv

  def Choices.get (idx : chs.Idx) : O :=
    let ⟨i, h_i⟩ := idx
    let _ : i < chs.choices.size := by
      rw [← chs.inv]
      exact h_i
    chs.choices[i]

  instance (chs : Choices O count) : Coe (Fin chs.choices.size) chs.Idx where
    coe i := by
      let ⟨i, h_i⟩ := i
      exact ⟨i, chs.inv ▸ h_i⟩

  instance : GetElem (Choices O count) Nat O (fun chs idx => idx < chs.count) where
    getElem chs idx idx_lt_count :=
      chs.get ⟨idx, idx_lt_count⟩

  instance : GetElem (Choices O count) (Fin count) O (fun chs _ => count ≤ chs.count) where
    getElem chs idx count_le_count :=
      let legit : idx.1 < chs.count :=
        Nat.lt_of_lt_of_le idx.2 count_le_count
      chs.get ⟨idx.1, legit⟩

  section
    variable
      (f : chs.Idx → O → Prop)

    @[simp]
    abbrev Choices.all : Prop :=
      ∀ (idx : chs.Idx), f idx chs[idx]

    @[simp]
    abbrev Choices.any : Prop :=
      ∃ (idx : chs.Idx), f idx chs[idx]
  end



  section map
    variable
      (f : chs.Idx → O → O')

    def Choices.map : Choices O' count := {
      choices :=
        chs.choices.mapIdx (fun idx o => f idx o)
      inv := by
        simp [Array.size_mapIdx, chs.inv]
    }

    def Choices.get_map
      (i : chs.Idx)
    : (chs.map f).get i = f i (chs.get i)
    := by
      simp [map, get, invariant]
    def Choices.getElem_map
      (i : chs.Idx)
    : (chs.map f)[i] = f i chs[i]
    := by
      simp [GetElem.getElem, get_map]
  end map
end



/-! ## Collective Choice Rule (CCR) -/
section ccr
  abbrev Ccr (Src Tgt : Type u) (count : ℕ) : Type u :=
    Choices Src count → Tgt

  /-- Definition 2.1. -/
  abbrev Ccr.OrderToProto (α : Type u) (count : ℕ) : Type u :=
    Ccr (Order α) (ProtoOrder α) count

  /-- Definition 2.2. -/
  abbrev Ccr.is_decisive
    (ccr : Ccr.OrderToProto α count)
  : Prop :=
    ∀ (chs : Choices.Ordered α count), Total (ccr chs).le
end ccr



section pareto
  variable
    (α : Type u)
    [DecidableEq α]
    {O : Type u}
    (chs : Choices O count)


  abbrev Pareto.le
    [C : Coe O (ProtoOrder α)]
    (x y : α)
  : Prop :=
    chs.all
      fun _ o =>
        (C.coe o).le x y

  abbrev Pareto.lt
    [_C : Coe O (ProtoOrder α)]
    (x y : α)
  : Prop :=
    Pareto.le α chs x y ∧ ¬ Pareto.le α chs y x

  /-- Definition 2.3.

  Since Pareto preference and indifference are defined in the standard way, we just define `≤` and
  let the proto-order structure generate the rest.
  -/
  @[simp]
  protected abbrev Pareto.ProtoOrder [C : Coe O (ProtoOrder α)] : ProtoOrder α where
    le := Pareto.le α chs
    toDecidableEq := inferInstance
    toDecidableRel := by
      simp only [DecidableRel]
      let _ : ∀ (i : chs.Idx), DecidableRel (C.coe chs[i]).le := by
        intro i
        exact C.coe chs[i] |>.toDecidableRel
      exact inferInstance

  @[simp]
  abbrev Pareto.mkProtoOrder
    {α : Type u} [DecidableEq α]
    (chs : Choices.ProtoOrdered α count)
  : ProtoOrder α :=
    Pareto.ProtoOrder (C := ⟨fun o => o⟩) chs

  @[simp]
  protected abbrev Pareto.Preorder [C : Coe O (Order α)] : Preorder α where
    toProtoOrder :=
      Pareto.ProtoOrder chs (C := ⟨fun X => C.coe X |>.toProtoOrder⟩)
    le_refl' x := by
      intro i
      exact C.coe chs[i] |>.le_refl
    le_trans' x y z := by
      simp only [Pareto.ProtoOrder]
      intro xy yz i
      exact C.coe chs[i] |>.le_trans (xy i) (yz i)

  @[simp]
  abbrev Pareto.mkPreorder
    {α : Type u} [DecidableEq α]
    (chs : Choices.Ordered α count)
  : Preorder α :=
    Pareto.Preorder (C := ⟨fun o => o⟩) chs
  
  abbrev lemma_2_a :=
    @Pareto.Preorder

  theorem Pareto.total_iff
    [C : Coe O (Order α)]
    [Inhabited chs.Idx]
  : Total (Pareto.Preorder α chs |>.le)
  ↔ ∀ x y,
    (∃ (i : chs.Idx), C.coe chs[i] |>.lt x y)
    → ∀ (i : chs.Idx), C.coe chs[i] |>.le x y
  := by
    simp [Pareto.Preorder, Pareto.ProtoOrder]
    constructor
    · intro total_le x y i' _i'_x_le_y i'_not_y_le_x
      let total_x_y := total_le x y
      cases total_x_y with
      | inl xy =>
        exact xy
      | inr yx =>
        let _ := yx i'
        contradiction
    · intro h
      intro x y
      if h_xy : ∀ (i : chs.Idx), (C.coe chs[i]).le x y then
        apply Or.inl h_xy
      else if h_yx : ∀ (i : chs.Idx), (C.coe chs[i]).le y x then
        apply Or.inr h_yx
      else
        simp [not_forall] at h_xy h_yx
        cases h_xy with | intro i₁ nxy₁ =>
        cases h_yx with | intro i₂ nyx₂ =>
        let xy₂ : (C.coe chs[i₂]).le x y := by
          let res := (C.coe chs[i₂]).le_total' x y
          simp [nyx₂] at res
          exact res
        let xy₁ :=
          h x y i₂ xy₂ nyx₂ i₁
        contradiction

  abbrev lemma_2_b := @Pareto.total_iff



  /-- Definition 2.4, "double-bar `P`". -/
  abbrev Pareto.strongLt
    [C : Coe O (Order α)]
    (x y : α)
  : Prop :=
    chs.all fun _ o =>
      let _ := C.coe o
      x < y



  theorem Pareto.lt_asymm
    [C : Coe O (Order α)]
  : ∀ x y, (Pareto.Preorder α chs).lt x y → ¬ (Pareto.Preorder α chs).lt y x := by
    simp [Pareto.Preorder, Pareto.ProtoOrder]
    intro x y _all_xy i₁ nyx₁ all_yx
    let yx₁ := all_yx i₁
    contradiction
  
  theorem Pareto.lt_trans
    [_C : Coe O (Order α)]
  : Transitive (Pareto.Preorder α chs).lt :=
    fun _ _ _ => Pareto.Preorder α chs |>.lt_trans

  theorem Pareto.strongLt_asymm
    [C : Coe O (Order α)]
    [Inhabited chs.Idx]
  : ∀ x y, Pareto.strongLt α chs x y → ¬ Pareto.strongLt α chs y x := by
    simp [strongLt]
    intro x y all_x_lt_y
    let i : chs.Idx := default
    exists i
    intro n_y_lt_x
    apply n_y_lt_x.right
    exact all_x_lt_y i |>.left

  theorem Pareto.strongLt_trans
    [C : Coe O (Order α)]
  : Transitive (Pareto.strongLt α chs) := by
    simp [strongLt]
    intro x y z all_lt_x_y all_lt_y_z i
    apply (C.coe chs[i]).lt_trans (all_lt_x_y i) (all_lt_y_z i)



  variable
    {α : Type u}
    [DecidableEq α]
    {O : Type u}
    {count : ℕ}
    (chs : Choices O count)



  abbrev lemma_2_c
    [Coe O (Order α)]
    [Inhabited α]
    [Inhabited chs.Idx]
  :=
    And.intro (Pareto.lt_trans α chs)
    $ And.intro (Pareto.lt_asymm α chs)
    $ And.intro (Pareto.strongLt_trans α chs)
    $ Pareto.strongLt_asymm α chs

  theorem Pareto.lt_of_strong_lt
    [C : Coe O (Order α)]
    [Inhabited chs.Idx]
  : ∀ (x y : α), Pareto.strongLt α chs x y → (Pareto.Preorder α chs).lt x y := by
    simp [strongLt, Pareto.ProtoOrder, ProtoOrder.lt_def, Pareto.Preorder]
    intro x y x_strong_y
    constructor
    · intro i
      exact x_strong_y i |>.left
    · let i : chs.Idx := default
      exists i
      exact x_strong_y i |>.right
  
  abbrev lemma_2_d :=
    @Pareto.lt_of_strong_lt


 
  /-- Definition 2.5. -/
  abbrev Ccr.is_pareto_inclusive
    (ccr : Ccr.OrderToProto α count)
  : Prop :=
    let _ : Coe (Order α) (ProtoOrder α) :=
      ⟨fun o => o.toProtoOrder⟩
    ∀ (chs : Choices (Order α) count),
      Pareto.ProtoOrder α chs ⊆ ccr chs

  /-- Definition 2.6. -/
  abbrev Choices.is_pareto_optimal
    (chs : Choices.Ordered α count)
    (x : α)
  : Prop :=
    ¬ ∃ (y : α), (Pareto.mkPreorder chs).lt y x



  theorem lemma_2_e
    [Finite α]
    [Inhabited α]
    (chs : Choices.Ordered α count)
  : ∃ (x : α), chs.is_pareto_optimal x := by
    let P := Pareto.mkPreorder chs
    let max := lemma_1_b α
    let ⟨max, M_max⟩ := max
    exists max
end pareto

