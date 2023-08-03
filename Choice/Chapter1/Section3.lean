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
      let max := R.listMaxP (hd'::tl) (List.cons_ne_nil _ _)
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
        R.listMaxP_in_list (hd'::tl) (List.cons_ne_nil _ _)
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
      simp [h_a_eq, listMaxP, R.P_irrefl]
    | hd::hd'::tl => by
      let hd_in_dom :=
        allInDom hd (List.Mem.head (hd'::tl))
      unfold listMaxP ; simp only []
      let sub_in_dom :=
        let inList' := R.listMaxP_in_list (hd'::tl) (List.cons_ne_nil _ _)
        allInDom _ (List.Mem.tail hd inList')
      split <;> cases h_a_dom
      · intro h
        exact h.right h.left
      case inl.tail h_hd_P_sub h_a_dom =>
        let h_not_a_P_sub :=
          R.listMaxP_max (hd'::tl) (List.cons_ne_nil _ _) a h_a_dom
            (fun a h => allInDom a $ List.Mem.tail hd h)
        intro h_a_P_hd
        apply h_not_a_P_sub
        apply R.P.trans (a := a) (a' := hd) h_a_P_hd h_hd_P_sub
      · assumption
      case inr.tail h_hd_P_sub h_a_dom =>
        apply R.listMaxP_max (hd'::tl) (List.cons_ne_nil _ _) a h_a_dom
          (fun a h => allInDom a $ List.Mem.tail hd h)

  def Rel.getMax
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : α :=
    R.listMaxP R.listDom R.nemptyListDom
  
  instance Rel.getMax_InDom
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : R.InDom R.getMax :=
    let h := R.listMaxP_in_list R.listDom R.nemptyListDom
    Rel.InDom.ofInList h

  /-- Closest equivalent to lemma 1.b.
  
  Original formulation omits the necessary assumption that `R.Dom ≠ ∅`. -/
  theorem Rel.getMax_max
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : R.max R.getMax := by
    simp only [Rel.M, Membership.mem, max]
    apply And.intro R.getMax_InDom
    intro a instInDom_a
    apply R.listMaxP_max R.listDom R.nemptyListDom a instInDom_a.toInList
      (fun _ h_a_dom => InDom.ofInList h_a_dom)



  /- Lemma 1.b.
  
  Original formulation omits the necessary assumption that `R.Dom ≠ ∅`. -/
  theorem Rel.lemma_1_b
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : R.max R.getMax :=
    R.getMax_max
end lemma_1_b



section lemma_1_c
  theorem Rel.lemma_1_c_mp₁
    (R : Rel α)
    [R.Refl]
    {a a' : α} [aInDom : R.InDom a] [R.InDom a']
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
  : R.P a a' → R.C a := by
    intro h_a_P_a'
    apply And.intro aInDom
    intro x xInDom
    cases h_Dom x with
    | inl h_eq =>
      rw [h_eq]
      exact R.refl
    | inr h_eq =>
      rw [h_eq]
      exact h_a_P_a'.left

  theorem Rel.lemma_1_c_mp₂
    (R : Rel α)
    {a a' : α} [R.InDom a] [R.InDom a']
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
  : R.P a a' → ((x : α) → [R.InDom x] → R.C x → x = a) := by
    intro h_a_P_a' x xInDom h_x_max
    cases h_Dom x
    case inl _ =>
      assumption
    case inr h_eq =>
      let h_not_a_R_a' := h_a_P_a'.right
      let h_a_R_a' := h_eq ▸ h_x_max.right a
      contradiction

  theorem Rel.lemma_1_c_mpr
    (R : Rel α)
    [R.Refl]
    [Set.Finite R.Dom]
    {a a' : α} [R.InDom a] [a'InDom : R.InDom a']
    (h_ne : a ≠ a')
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
    (h₁ : R.C a)
    (h₂ : (x : α) → [R.InDom x] → R.C x → x = a)
  : R.P a a' := by
    simp
    apply And.intro $ h₁.right a'
    intro h_a'_R_a
    let h : R.C a' := by
      apply And.intro a'InDom
      intro x xInDom
      cases h_Dom x
      case inl h_eq => rw [h_eq] ; exact h_a'_R_a
      case inr h_eq => rw [h_eq] ; exact R.refl
    rw [h₂ a' h] at h_ne
    contradiction

  /-- Lemma 1.c.

  Assumption `h_ne` is not in the book, but it is necessary for the theorem's `Iff.mpr`, since `R.P`
  is not reflexive. The book version uses `[x, y]` for the set composed of `x` and `y`, which maybe
  indicates that `x` and `y` should be different. -/
  theorem Rel.lemma_1_c
    (R : Rel α)
    [R.Refl]
    [Set.Finite R.Dom]
    {a a' : α} [R.InDom a] [R.InDom a']
    (h_ne : a ≠ a')
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
  : R.P a a' ↔ ( R.C a ∧ ((x : α) → [R.InDom x] → R.C x → x = a)) := by
    constructor
    · intro h_a_P_a'
      constructor
      · apply R.lemma_1_c_mp₁ h_Dom h_a_P_a'
      · apply R.lemma_1_c_mp₂ h_Dom h_a_P_a'
    · intro conj
      let ⟨h_C_a, h⟩ := conj
      apply R.lemma_1_c_mpr h_ne h_Dom h_C_a h
end lemma_1_c



section lemma_1_d
  /-- Lemma 1.d. -/
  theorem Rel.lemma_1_d
    (R : Rel α)
    [R.PreOrder]
    (best : α)
    [R.InDom best]
    (h_best : R.C best)
  : ∀ (a : α), [R.InDom a] → R.C a ↔ R.M a := by
    intro aMax aMaxInDom
    constructor
    · exact R.max_of_best aMax -- `aMax` is actually a *best* here, not a *max*
    · simp only [M, C]
      unfold Rel.max
      unfold Rel.best
      intro h_Max
      let h_aMax_R_best : R aMax best := by
        let h_best_R_aMax :=
          h_best.right aMax
        let h_not_best_P_aMax :=
          h_Max.right best
        simp [P] at h_not_best_P_aMax
        exact h_not_best_P_aMax h_best_R_aMax |> Decidable.not_not.mp
      apply And.intro aMaxInDom
      intro y yInDom
      apply R.trans (a' := best) h_aMax_R_best $ h_best.right y
end lemma_1_d



section lemma_1_e
  theorem Rel.lemma_1_e_mpr
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
  : (∀ (a : α), [R.InDom a] → R.C a ↔ R.M a)
  → (x y : α) → [R.InDom x] → [R.InDom y]
  → R.M x → R.M y
  → R.I x y := fun h_C_eq_M x y _ _ h_Max_x h_Max_y =>
    let h_C_x :=
      (h_C_eq_M x).mpr h_Max_x
    let h_C_y :=
      (h_C_eq_M y).mpr h_Max_y
    ⟨h_C_x.right y, h_C_y.right x⟩

  theorem Rel.lemma_1_e_mp
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : (∀ (x y : α), [R.InDom x] → [R.InDom y] → R.M x → R.M y → R.I x y)
  → ∀ (a : α), [R.InDom a] → R.C a ↔ R.M a := by
    intro get_I_of_M max maxInDom
    apply Iff.intro $ R.max_of_best max
    intro h_M_max
    simp
    simp [Membership.mem]
    apply And.intro maxInDom
    intro a' _
    let h := h_M_max.right a'
    simp only [Rel.P, Decidable.not_and_iff_or_not] at h
    cases h
    case inl h_not_a'_R_a =>
      apply Decidable.byContradiction
      sorry
    case inr h_a_R_a' =>
      apply Decidable.byContradiction
      intro h
      exact h_a_R_a' h
end lemma_1_e
