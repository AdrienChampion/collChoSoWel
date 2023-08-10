import Choice.Chapter1.Section1



/-! # Section 1.2 -/
namespace Choice



section
  variable
    {α : Type u}
    [R : Preorder α]
  
  /-- Custom (computable) notion of finiteness.
  
  Implies `_root_.Finite`. -/
  class Finite (α : Type u) where
    elems : List α
    toℕ : α → Fin elems.length
    sanity_α : ∀ (a : α), elems.get (toℕ a) = a
    sanity_fin : ∀ (idx : Fin elems.length), toℕ (elems.get idx) = idx

  abbrev Finite.card (α : Type u) [F : Finite α] : ℕ := 
    F.elems.length
  
  abbrev Finite.Idx (α : Type u) [F : Finite α] :=
    Fin F.card

  abbrev Finite.invℕ [F : Finite α] : F.Idx → α :=
    F.elems.get
  
  abbrev Finite.all_in_elems [F : Finite α] : ∀ (a : α), a ∈ F.elems := by
    intro a
    let h_get_a := F.sanity_α a
    rw [←h_get_a]
    apply List.get_mem



  def Finite.bijℕ [I : Finite α] : α ≃ Fin I.card where
    toFun := I.toℕ
    invFun := I.invℕ
    left_inv := I.sanity_α
    right_inv := I.sanity_fin
  
  instance [I : Finite α] : _root_.Finite α :=
    .intro I.bijℕ

  def wellFoundedP
    [Preorder α]
    [Finite α]
  : WellFoundedLT α :=
    Finite.to_wellFoundedLT



  def Finite.zero_lt_card
    [F : Finite α]
    [I : Inhabited α]
  : 0 < F.card := by
    let idx := F.toℕ default
    cases h : F.elems.length with
    | zero =>
      rw [h] at idx
      let ⟨n, h⟩ := idx
      contradiction
    | succ n =>
      simp [card]
      simp [h]

  def Finite.all_iff_elems
    [F : Finite α]
    {P : α → Prop}
  : (∀ a, P a) ↔ (∀ a ∈ F.elems, P a) := ⟨
    fun h a _ =>
      h a,
    fun h a =>
      let h := h a
      h (F.all_in_elems a)
  ⟩
end



section
  variable
    {α : Type u}
    [R : Preorder α]
    [F : Finite α]
    [I : Inhabited α]



  abbrev Preorder.is_max (a : α) : Prop :=
    ¬ ∃ (b : α), b < a
  abbrev Preorder.M : Set α :=
    is_max

  def Preorder.isMax (a : α) : Bool :=
    F.elems.all (¬ · < a)
  
  theorem Preorder.isMax_iff_in_M : R.isMax a ↔ a ∈ R.M := ⟨
    by
      simp [Membership.mem, Set.Mem, isMax]
      intro isMax_a b
      exact isMax_a b (F.all_in_elems b),
    by
      simp [Membership.mem, Set.Mem, isMax]
      intro h b _
      exact h b
  ⟩

  instance : Decidable (a ∈ R.M) :=
    if h : R.isMax a then
      Preorder.isMax_iff_in_M.mp h
      |> isTrue
    else
      Preorder.isMax_iff_in_M.not.mp h
      |> isFalse

  def Preorder.maxCex : a ∉ M → ∃ (b : α), b < a := by
    simp [Membership.mem, Set.Mem, M, is_max]
    intro b h
    exact ⟨b, h⟩
  
  def Preorder.maxCexInv : (∃ (b : α), b < a) → a ∉ M := by
    simp [Membership.mem, Set.Mem, M, is_max]
    intro b h
    exact ⟨b, h⟩
  
  def Preorder.not_getMax_iff_cex : a ∉ M ↔ ∃ (b : α), b < a :=
    ⟨maxCex, maxCexInv⟩ 



  abbrev Preorder.is_best (a : α) : Prop :=
    ∀ (b : α), a ≤ b
  abbrev Preorder.C : Set α :=
    is_best

  def Preorder.isBest (a : α) : Bool :=
    F.elems.all (a ≤ ·)
  
  theorem Preorder.isBest_iff_in_C : isBest a ↔ a ∈ R.C := ⟨
    by
      simp [isBest]
      intro isBest_a b
      exact isBest_a b (F.all_in_elems b),
    by
      simp [isBest]
      intro h b _
      exact h b
  ⟩

  instance : Decidable (a ∈ R.C) :=
    if h : R.isBest a then
      Preorder.isBest_iff_in_C.mp h
      |> isTrue
    else
      Preorder.isBest_iff_in_C.not.mp h
      |> isFalse

  def Preorder.bestCex : a ∉ C → ∃ (b : α), ¬ a ≤ b := by
    simp [Membership.mem, Set.Mem, C, is_best]
    intro b h
    exact ⟨b, h⟩
  
  def Preorder.bestCexInv : (∃ (b : α), ¬ a ≤ b) → a ∉ C := by
    simp [Membership.mem, Set.Mem, C, is_best]
    intro b h
    exact ⟨b, h⟩
  
  def Preorder.not_getBest_iff_cex : a ∉ C ↔ ∃ (b : α), ¬ a ≤ b :=
    ⟨bestCex, bestCexInv⟩ 
end