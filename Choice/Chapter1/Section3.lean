import Choice.Chapter1.Section2



/-! # Section 1.3 -/
namespace Choice



/-! ### Lemma `1*a` -/
section lemma_1_a
  variable
    {R : Rel α}
    [I : R.PreOrder]
    {x y z : α} [R.InDom x] [R.InDom y] [R.InDom z]

  theorem Rel.PreOrder.trans_I : R.I x y → R.I y z → R.I x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      I.trans h_yz.right h_xy.right
    ⟩

  theorem Rel.PreOrder.trans_PI : R.P x y → R.I y z → R.P x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      fun h_zx => h_xy.right $ I.trans h_yz.left h_zx
    ⟩

  theorem Rel.PreOrder.trans_IP : R.I x y → R.P y z → R.P x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      fun h_zx => h_yz.right $ I.trans h_zx h_xy.left
    ⟩
  
  theorem Rel.PreOrder.trans_P : R.P x y → R.P y z → R.P x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      fun h_zx => h_yz.right $ I.trans h_zx h_xy.left
    ⟩
end lemma_1_a



/-! ### Lemma `1*b` -/
section lemma_1_b
  def Rel.listMaxP
    (R : Rel α)
    (l : List α)
    (_h_nempty : l ≠ [])
  : α :=
    match l with
    | [max] => max
    | hd::hd'::tl =>
      let max := R.listMaxP (hd'::tl) List.cons_ne_nil
      if R.P hd max then hd else max

  theorem Rel.listMaxP_in_list
    (R : Rel α)
    (l : List α)
    (h_nempty : l ≠ [])
  : (R.listMaxP l h_nempty) ∈ l :=
    match l with
    | [max] => by
      simp only [listMaxP, Membership.mem, List.Mem.head]
    | hd::hd'::tl => by
      let ih :=
        R.listMaxP_in_list (hd'::tl) List.cons_ne_nil
      unfold listMaxP
      simp [Membership.mem]
      split
      · exact List.Mem.head (hd'::tl)
      · apply List.Mem.tail
        exact ih

  theorem Rel.listMaxP_max
    (R : Rel α)
    [R.PreOrder]
    (l : List α)
    (h_nempty : l ≠ [])
    (a : α)
    (h_a_dom : a ∈ l)
    (allInDom : (a : α) → a ∈ l → R.InDom a)
  : ¬ R.P a (R.listMaxP l h_nempty) :=
    let h_a_in_dom :=
      allInDom a h_a_dom
    match l with
    | [max] => by
      let h_a_eq : a = max := by
        cases h_a_dom ; rfl ; contradiction
      simp [h_a_eq, listMaxP]
      intro h
      exact h.right h.left
    | hd::hd'::tl => by
      let hd_in_dom :=
        allInDom hd (List.Mem.head (hd'::tl))
      unfold listMaxP ; simp
      let sub_in_dom :=
        let inList' := R.listMaxP_in_list (hd'::tl) List.cons_ne_nil
        allInDom _ (List.Mem.tail hd inList')
      split <;> cases h_a_dom
      · intro h
        exact h.right h.left
      case inl.tail h_hd_P_sub h_a_dom =>
        let h_not_a_P_sub :=
          R.listMaxP_max (hd'::tl) List.cons_ne_nil a h_a_dom
            (fun a h => allInDom a $ List.Mem.tail hd h)
        intro h_a_P_hd
        apply h_not_a_P_sub
        apply R.P.trans (a := a) (a' := hd) h_a_P_hd h_hd_P_sub
      · assumption
      case inr.tail h_hd_P_sub h_a_dom =>
        apply R.listMaxP_max (hd'::tl) List.cons_ne_nil a h_a_dom
          (fun a h => allInDom a $ List.Mem.tail hd h)

  def Rel.getMax
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : α :=
    R.listMaxP R.listDom R.nemptyListDom

  theorem Rel.getMax_max
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : R.getMax ∈ R.M := by
    simp [Rel.M, Membership.mem, Set.mem]
    intro a instInDom_a
    apply R.listMaxP_max R.listDom R.nemptyListDom a instInDom_a.toInList
      (fun _ h_a_dom => R.inListToInDom h_a_dom)



  /-- Lemma 1.b.
  
  Original formulation omits that `R.Dom ≠ ∅` -/
  theorem Rel.existsMax
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : ∃ (max : α), max ∈ R.M :=
    ⟨R.getMax, R.getMax_max⟩
end lemma_1_b