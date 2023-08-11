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



  def Finite.elems_not_nil
    [F : Finite α]
    [I : Inhabited α]
  : F.elems ≠ [] := by
    let h := F.all_in_elems default
    intro h_nil
    rw [h_nil] at h
    apply List.mem_nil_iff default |>.mp h

  def Finite.zero_lt_card
    [F : Finite α]
    [I : Inhabited α]
  : 0 < F.card := by
    let not_nil := F.elems_not_nil
    simp [card]
    match h : F.elems with
    | [] =>
      rw [h] at not_nil
      contradiction
    | _::_ =>
      simp [List.length]

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
  
  theorem Preorder.M_def : a ∈ R.M ↔ ¬ ∃ (b : α), b < a := by
    simp [Membership.mem, Set.Mem]

  def Preorder.isMax (a : α) : Bool :=
    F.elems.all (¬ · < a)
  
  theorem Preorder.isMax_iff_in_M : R.isMax a ↔ a ∈ R.M := ⟨
    by
      simp [M_def, isMax]
      intro isMax_a b
      exact isMax_a b (F.all_in_elems b),
    by
      simp [M_def, isMax]
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

  theorem Preorder.maxCex : a ∉ M → ∃ (b : α), b < a := by
    simp [M_def]
    intro b h
    exact ⟨b, h⟩
  
  theorem Preorder.maxCexInv : (∃ (b : α), b < a) → a ∉ M := by
    simp [M_def]
    intro b h
    exact ⟨b, h⟩
  
  theorem Preorder.not_max_iff_cex : a ∉ M ↔ ∃ (b : α), b < a :=
    ⟨maxCex, maxCexInv⟩




  abbrev Preorder.is_best (a : α) : Prop :=
    ∀ (b : α), a ≤ b
  abbrev Preorder.C : Set α :=
    is_best
  
  theorem Preorder.C_def : a ∈ R.C ↔ ∀ (b : α), a ≤ b := by
    simp [Membership.mem, Set.Mem]

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

  theorem Preorder.bestCex : a ∉ C → ∃ (b : α), ¬ a ≤ b := by
    simp [C_def, is_best]
    intro b h
    exact ⟨b, h⟩
  
  theorem Preorder.bestCexInv : (∃ (b : α), ¬ a ≤ b) → a ∉ C := by
    simp [C_def]
    intro b h
    exact ⟨b, h⟩
  
  theorem Preorder.not_best_iff_cex : a ∉ C ↔ ∃ (b : α), ¬ a ≤ b :=
    ⟨bestCex, bestCexInv⟩



  theorem Preorder.best_is_max : R.C ⊆ R.M
    | best, C_best, ⟨cex, b_lt_cex⟩ => by
      rw [R.lt_def] at b_lt_cex
      apply b_lt_cex.right (C_best cex)



  def Preorder.getMax : α :=
    aux F.elems F.elems_not_nil
  where
    aux (l : List α) (_ : l ≠ []) :=
      match l with
      | [a] => a
      | a::b::tl =>
        let sub := aux (b::tl) (by simp)
        if a < sub then a else sub

  def Preorder.getMax.aux_legit
    {l : List α} {h_ne_nil : l ≠ []} {max : α}
  : max = getMax.aux l h_ne_nil → ∀ b ∈ l, ¬ b < max :=
    match h : l with
    | [] => by contradiction
    | [a] => by
      simp [aux]
      intro h
      rw [h]
      apply irrefl
    | hd::hd'::tl => by
      simp [aux]
      let sub := aux (hd'::tl) (List.cons_ne_nil hd' tl)
      let ih :=
        aux_legit
          (l := hd'::tl)
          (h_ne_nil := List.cons_ne_nil hd' tl)
          (max := sub)
          rfl
      if hd_lt_sub : hd < sub then
        simp [hd_lt_sub]
        intro h ; rw [h]
        simp
        apply And.intro
        · intro absurd
          apply ih hd' (List.mem_cons_self hd' tl)
          apply Trans.trans absurd hd_lt_sub
        · intro a a_in_tl
          intro a_lt_hd
          apply ih a (List.Mem.tail hd' a_in_tl)
          apply Trans.trans a_lt_hd hd_lt_sub
      else
        simp [hd_lt_sub]
        intro max_def
        simp [max_def]
        apply And.intro hd_lt_sub
        apply And.intro (ih hd' (List.mem_cons_self hd' tl))
        intro a a_in_tl
        apply ih a (List.Mem.tail hd' a_in_tl)
  
  def Preorder.getMax_in_M
    {max : α}
  : max = R.getMax → max ∈ M := by
    simp [getMax, M_def]
    intro max_def
    let h := getMax.aux_legit max_def
    intro a
    apply h a (F.all_in_elems a)
end