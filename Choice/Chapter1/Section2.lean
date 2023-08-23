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
    elems_nodup : elems.Nodup
    toℕ : α → Fin elems.length
    sanity_α : ∀ (a : α), elems.get (toℕ a) = a
    sanity_fin : ∀ (idx : Fin elems.length), toℕ (elems.get idx) = idx

  abbrev Finite.card (α : Type u) [F : Finite α] : ℕ := 
    F.elems.length
  
  abbrev Finite.Idx (α : Type u) [F : Finite α] :=
    Fin F.card

  abbrev Finite.invℕ [F : Finite α] : F.Idx → α :=
    F.elems.get
  
  abbrev Finite.all_in_elems (F : Finite α) : ∀ (a : α), a ∈ F.elems := by
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

  def Finite.wellFoundedP
    [Preorder α]
    [Finite α]
  : WellFoundedLT α :=
    Finite.to_wellFoundedLT

  instance instWellFounded_of_Finite_Preorder
    [R : Preorder α]
    [F : Finite α]
  : IsWellFounded α R.lt :=
    F.wellFoundedP
  
  instance
    [R : Preorder α]
    [_F : Finite α]
  : WellFoundedRelation α where
    rel := R.lt
    wf := instWellFounded_of_Finite_Preorder.wf



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

  protected def Finite.subElems
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
  : List S :=
    aux F.elems
  where aux : List α → List S
    | [] => []
    | hd::tl =>
      let sub := aux tl
      if h : hd ∈ S then ⟨hd, h⟩ :: sub else sub

  protected def Finite.subElems.aux_all_in_subElems
    -- I think we could drop this, but too tired right now
    [DecidableEq α]
    [_F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    (l : List α)
  : ∀ (a : S), a.1 ∈ l ↔ a ∈ Finite.subElems.aux S l := by
    induction l with
    | nil =>
      simp [aux]
    | cons hd tl ih =>
      simp [aux]
      intro a b
      split
      case inl hd_in_S =>
        if a_eq_hd : a = hd then
          simp [a_eq_hd]
        else
          simp [a_eq_hd]
          apply ih ⟨a, b⟩
      case inr _ =>
        if a_eq_hd : a = hd then
          rw [a_eq_hd] at b
          contradiction
        else
          simp [a_eq_hd]
          apply ih ⟨a, b⟩
  protected def Finite.all_in_subElems
    [DecidableEq α]
    [F : Finite α]
    {S : Set α}
    [∀ a, Decidable (a ∈ S)]
  : ∀ (a : S), a ∈ F.subElems S := by
    intro a
    let h :=
      Finite.subElems.aux_all_in_subElems S F.elems a
    simp [F.all_in_elems] at h
    exact h

  protected def Finite.subElems.aux_nodup
    [_F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    (l : List α)
    (l_nodup : l.Nodup)
  : Finite.subElems.aux S l |>.Nodup := by
    induction l with
    | nil =>
      simp [aux]
    | cons hd tl ih =>
      simp [aux]
      split
      case inl hd_in_S =>
        apply List.Nodup.cons
        · intro hd_in_aux_tl
          let hd_in_tl := subElems.aux_all_in_subElems S tl ⟨hd, hd_in_S⟩
          let hd_in_tl := hd_in_tl.mpr hd_in_aux_tl
          simp [Coe.coe] at hd_in_tl
          apply List.not_nodup_cons_of_mem hd_in_tl
          exact l_nodup
        · apply ih
          cases l_nodup
          assumption
      case inr hd_notin_S =>
        apply ih
        cases l_nodup
        assumption
  protected def Finite.subElems_nodup
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
  : F.subElems S |>.Nodup :=
    Finite.subElems.aux_nodup S F.elems F.elems_nodup

  protected def Finite.subToℕ'
    [DecidableEq α]
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    (a : S)
  : Nat :=
    aux (F.subElems S) 0 (F.all_in_subElems a)
  where
    aux
      (l : List S) (idx : Nat)
      (a_in_l : a ∈ l)
    : Nat :=
      match l with
      | [] => by
        contradiction
      | hd :: tl =>
        if a_eq_hd : a = hd then
          idx
        else
          aux tl (idx + 1) (by cases a_in_l ; contradiction ; assumption)

  protected def Finite.subToℕ'.aux_succ
    [DecidableEq α]
    [_F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    {l : List S}
  :
    ∀ (a : S),
      (a_in_l : a ∈ l)
      → (idx : Nat)
      → Finite.subToℕ'.aux S a l idx.succ a_in_l = (Finite.subToℕ'.aux S a l idx a_in_l).succ
  := by
    intro a a_in_l
    induction l with
    | nil =>
      contradiction
    | cons hd tl ih =>
      intro idx
      simp [aux]
      split
      case inl a_eq_hd =>
        rfl
      case inr a_ne_hd =>
        apply ih

  protected def Finite.subToℕ'.aux_fin
    [DecidableEq α]
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    {l : List S}
  :
    ∀ (a : S),
      (a_in_l : a ∈ l)
      → Finite.subToℕ'.aux S a l 0 a_in_l < l.length
  := by
    intro a a_in_l
    induction l with
    | nil =>
      contradiction
    | cons hd tl ih =>
      simp [aux]
      split
      case inl a_eq_hd =>
        exact Nat.zero_lt_succ _
      case inr a_ne_hd =>
        cases a_in_l with
        | head => contradiction
        | tail _ a_in_tl =>
          rw [Finite.subToℕ'.aux_succ]
          apply Nat.succ_lt_succ_iff.mpr
          apply ih

  protected def Finite.subToℕ'.aux_sanity_α
    [DecidableEq α]
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    {l : List S}
    (a : S)
    (a_in_l : a ∈ l)
  : l.get ⟨(Finite.subToℕ'.aux S a l 0 a_in_l), Finite.subToℕ'.aux_fin S a a_in_l⟩ = a := by
    induction l with
    | nil =>
      contradiction
    | cons hd tl ih =>
      simp [aux]
      split
      case inl a_eq_hd =>
        simp [a_eq_hd]
      case inr a_ne_hd =>
        cases a_in_l ; contradiction
        case tail a_in_tl =>
          unfold List.get
          simp [Finite.subToℕ'.aux_succ]
          apply ih

  protected def Finite.subToℕ'.aux_sanity_fin
    {α : Type u}
    [DecidableEq α]
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    {l : List S}
    (l_nodup : l.Nodup)
    (idx : Fin l.length)
  :
    (
      Finite.subToℕ'.aux
        S (l.get idx) l 0
        (by exact List.mem_iff_get.mpr ⟨idx, rfl⟩)
    ) = idx
  := by
    induction l with
    | nil =>
      let _ := idx.2
      contradiction
    | cons hd tl ih =>
      let ⟨idx, h_idx⟩ := idx
      simp [aux]
      split
      case inl a_eq_hd =>
        cases idx with
        | zero => rfl
        | succ idxSub =>
          exfalso
          unfold List.get at a_eq_hd
          cases l_nodup with | cons nodup_hd tl_nodup =>
          let get_tl_in_tl :=
            List.get_mem tl idxSub (by apply Nat.lt_of_succ_lt_succ ; exact h_idx)
          
          apply nodup_hd _ get_tl_in_tl
          rw [a_eq_hd]
      case inr a_ne_hd =>
        cases l_nodup with | cons nodup_hd tl_nodup =>
        let ih := ih tl_nodup
        simp [Finite.subToℕ'.aux_succ]
        cases idx with
        | zero =>
          exfalso
          apply a_ne_hd
          simp [List.get]
        | succ subIdx =>
          simp
          apply ih

  protected def Finite.subToℕ
    [DecidableEq α]
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
    (a : S)
  : Fin (F.subElems S).length :=
    let n := Finite.subToℕ' S a
    let a_in_subElems := Finite.all_in_subElems a
    let h := Finite.subToℕ'.aux_fin S a a_in_subElems
    ⟨n, h⟩
  
  protected def Finite.subToℕ_sanity_α
    [DecidableEq α]
    [F : Finite α]
    {S : Set α}
    [∀ a, Decidable (a ∈ S)]
    (a : S)
  : (F.subElems S).get (Finite.subToℕ S a) = a := by
    simp [Finite.subToℕ]
    apply Finite.subToℕ'.aux_sanity_α
  
  protected def Finite.subToℕ_sanity_fin
    [DecidableEq α]
    [F : Finite α]
    {S : Set α}
    [∀ a, Decidable (a ∈ S)]
    (idx : Fin (F.subElems S).length)
  : F.subToℕ S ((F.subElems S).get idx) = idx := by
    simp only [Finite.subToℕ, Finite.subToℕ']
    ext
    simp
    apply Finite.subToℕ'.aux_sanity_fin
    apply F.subElems_nodup

  def Finite.finiteSet
    [DecidableEq α]
    [F : Finite α]
    (S : Set α)
    [∀ a, Decidable (a ∈ S)]
  : Finite S where
    elems := F.subElems S
    elems_nodup := Finite.subElems_nodup S
    toℕ := Finite.subToℕ S
    sanity_α := Finite.subToℕ_sanity_α
    sanity_fin := Finite.subToℕ_sanity_fin

  instance
    [DecidableEq α]
    [F : Finite α]
    {S : Set α}
    [∀ a, Decidable (a ∈ S)]
  : Finite S :=
    F.finiteSet S
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

  def Preorder.getMaxCex
    (a : α)
    (not_M_a : a ∉ M)
  : α :=
    match h : F.elems.find? fun b => b < a with
    | some cex => cex
    | none => by
      let tmp b := List.find?_eq_none.mp h b (F.all_in_elems b)
      let M_a : a ∈ M := by
        intro b
        let ⟨b, b_lt_a⟩ := b
        let tmp := tmp b
        simp at tmp
        contradiction
      contradiction
    
  theorem Preorder.getMaxCex_is_cex
    {a cex : α}
    {not_M_a : a ∉ M}
  : cex = R.getMaxCex a not_M_a → cex < a := by
    simp [getMaxCex]
    split
    case h_1 cex' h_cex' =>
      let h := List.find?_some h_cex'
      intro cex_def
      rw [cex_def]
      simp at h
      assumption
    case h_2 find?_none =>
      let tmp b := List.find?_eq_none.mp find?_none b (F.all_in_elems b)
      let M_a : a ∈ M := by
        intro b
        let ⟨b, b_lt_a⟩ := b
        let tmp := tmp b
        simp at tmp
        contradiction
      contradiction

  def Preorder.maxOfNotMax
    [R : Preorder α]
    [F : Finite α]
    (a : α)
    (not_M_a : a ∉ M)
  : α :=
    let cex := getMaxCex a not_M_a
    if h : cex ∈ M
    then cex
    else
      maxOfNotMax cex h
  termination_by maxOfNotMax _ R F a h =>
    a
  decreasing_by {
    simp_wf
    exact R.getMaxCex_is_cex rfl
  }

  lemma Preorder.maxOfNotMax_is_max
    [R : Preorder α]
    [F : Finite α]
    {a : α} {not_M_a : a ∉ M}
  : maxOfNotMax a not_M_a ∈ M := by
    unfold maxOfNotMax
    simp
    split <;> try assumption
    case inr h =>
      apply maxOfNotMax_is_max (a := getMaxCex a not_M_a)
  termination_by maxOfNotMax_is_max a _ =>
    a
  decreasing_by {
    simp_wf
    exact R.getMaxCex_is_cex rfl
  }

  lemma Preorder.maxOfNotMax_lt
    [R : Preorder α]
    [F : Finite α]
    {a : α} {not_M_a : a ∉ M}
  : maxOfNotMax a not_M_a < a := by
    unfold maxOfNotMax
    simp
    split
    case inl h =>
      apply R.getMaxCex_is_cex
      rfl
    case inr h =>
      let ih :=
        maxOfNotMax_lt (a := getMaxCex a not_M_a) (not_M_a := h)
      let h : getMaxCex a not_M_a < a :=
        R.getMaxCex_is_cex rfl
      apply Trans.trans ih h
  termination_by maxOfNotMax_lt a _ =>
    a
  decreasing_by {
    simp_wf
    exact R.getMaxCex_is_cex rfl
  }

  theorem Preorder.max_of_not_max
    [R : Preorder α]
    [_F : Finite α]
  : ∀ a, a ∉ M → ∃ max, max < a ∧ max ∈ R.M :=
    fun a not_M_a => ⟨
      R.maxOfNotMax a not_M_a,
      R.maxOfNotMax_lt,
      R.maxOfNotMax_is_max
    ⟩

  def Preorder.maxOf (a : α) : α :=
    if h : a ∈ R.M then a else getMaxCex a h
end



section sub
  abbrev Preorder.sub (P : Preorder α) (S : Set α) : Preorder S where
    le a b := P.le a.1 b.1
    lt a b := P.le a.1 b.1 ∧ ¬ P.le b.1 a.1
    Equiv a b := P.le a.1 b.1 ∧ P.le b.1 a.1
    lt_def := by
      simp [LT.lt]
    equiv_def := by
      simp [HasEquiv.Equiv]

    decidableRel _ _ := by
      simp [DecidableRel, LE.le]
      apply P.decidableRel
    decidableEq _a _b := by
      rw [Subtype.mk_eq_mk]
      apply P.decidableEq
    le_refl _ := by simp
    le_trans _ _ _ :=
      by
        unfold LE.le
        simp
        apply P.le_trans



  abbrev Order.sub (O : Order α) (S : Set α) : Order S where
    toPreorder :=
      O.toPreorder.sub S
    le_total a b :=
      O.le_total a.1 b.1
end sub
