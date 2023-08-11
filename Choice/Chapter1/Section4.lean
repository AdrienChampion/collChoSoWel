import Choice.Chapter1.Section3



/-! # Section 1.4 -/
namespace Choice



section subrelation
  /-- Definition 1*5, sub-relation, noted `R₁ ⊆ R₂`. -/
  abbrev Preorder.subrel (R₁ R₂ : Preorder α) : Prop :=
    ∀ a b, (R₁.le a b → R₂.le a b) ∧ (R₁.lt a b → ¬ R₂.le b a)
  
  instance : HasSubset (Preorder α) where
    Subset R₁ R₂ := R₁.subrel R₂

  /-- Definition 1*6, order/pre-order compatibility. -/
  abbrev Order.compatWith (O : Order α) (P : Preorder α) : Prop :=
    P.subrel O.toPreorder
  abbrev Preorder.compat (P : Preorder α) (O : Order α) : Prop :=
    P.subrel O.toPreorder
end subrelation



section lemma_1_f
  variable
    {α : Type u}
    [P : Preorder α]
  
  structure Preorder.Totalizer where
    added : List (α × α × List α)
    isNew : ∀ triplet ∈ added,
      let (a, b, _) := triplet
      ¬ a ≤ b ∧ ¬ b ≤ a
    isTrans : ∀ triplet ∈ added,
      let (_, b, cs) := triplet
      ∀ c, b ≤ c ↔ c ∈ cs

  def Preorder.mkTotalizer : P.Totalizer where
    added := []
    isNew := by intros ; contradiction
    isTrans := by intros ; contradiction



  variable
    (self : P.Totalizer)

  def Preorder.Totalizer.le (a b : α) : Prop :=
    a ≤ b ∨
    self.added.any
      fun (a', hd , tl) => a' = a ∧ (b = hd ∨ b ∈ tl)

  def Finite.leClosure [F : Finite α] (a : α) : List α :=
    aux F.elems
  where aux : List α → List α
    | [] => []
    | b::rest =>
      if a ≠ b ∧ a ≤ b
      then b :: (aux rest)
      else aux rest

  theorem Finite.leClosure.aux_in_list
    {a : α} {l res : List α}
  : res = aux a l → ∀ b ∈ res, b ∈ l := by
    intro res_def b b_in_res
    cases l with
    | nil =>
      simp [aux] at res_def
      rw [res_def] at b_in_res
      contradiction
    | cons hd tl =>
      simp only [aux] at res_def
      if h : hd = b then
        exact h ▸ List.Mem.head tl
      else if h : a ≠ hd ∧ a ≤ hd then
        simp [h] at res_def
        apply List.Mem.tail
        let sub := aux a tl
        let sub_def : sub = aux a tl := rfl
        apply aux_in_list sub_def
        rw [sub_def]
        rw [res_def] at b_in_res
        cases b_in_res <;> try contradiction
        assumption
      else
        simp [h] at res_def
        apply List.Mem.tail
        let sub := aux a tl
        let sub_def : sub = aux a tl := rfl
        apply aux_in_list sub_def
        rw [sub_def, ← res_def]
        assumption

  theorem Finite.leClosure.aux_post_mp
    {a : α} {l res : List α}
  : res = aux a l → ∀ b ∈ res, a ≠ b ∧ a ≤ b := by
    intro res_def
    induction l generalizing res with
    | nil =>
      simp [aux] at res_def
      rw [res_def]
      intro b _
      contradiction
    | cons hd tl ih =>
      simp [aux] at res_def
      split at res_def
      case inl h =>
        rw [res_def]
        intro b b_in_res
        cases b_in_res with
        | head tl => exact h
        | tail hd b_in_tl =>
          exact ih rfl b b_in_tl
      case inr h =>
        exact ih res_def

  theorem Finite.leClosure.aux_post_mpr
    {a : α} {l res : List α}
  : res = aux a l → ∀ b ∈ l, a ≠ b ∧ a ≤ b → b ∈ res := by
    intro res_def
    induction l generalizing res with
    | nil =>
      simp [aux] at res_def
      rw [res_def]
      intro b _
      contradiction
    | cons hd tl ih =>
      simp [aux] at res_def
      split at res_def
      case inl h =>
        rw [res_def]
        intro b b_in_res
        cases b_in_res with
        | head tl =>
          intro
          exact List.Mem.head _
        | tail hd b_in_tl =>
          intro h
          let b_in_sub := ih rfl b b_in_tl h
          exact List.Mem.tail _ b_in_sub
      case inr h =>
        intro b b_in_l h_b
        cases b_in_l with
        | head _ => contradiction
        | tail _ h =>
          exact ih res_def b h h_b

  theorem Finite.leClosure_post_mp
    [Finite α]
    {a : α} {res : List α}
  : res = leClosure a → ∀ b ∈ res, a ≠ b ∧ a ≤ b :=
    leClosure.aux_post_mp

  theorem Finite.leClosure_post_mpr
    [F : Finite α]
    {a : α} {res : List α}
  : res = leClosure a → (∀ b, a ≠ b ∧ a ≤ b → b ∈ res) :=
    fun res_def b h_b =>
      Finite.leClosure.aux_post_mpr res_def b (F.all_in_elems b) h_b

  theorem Finite.leClosure_post
    [F : Finite α]
    {a : α} {res : List α}
  : res = leClosure a → (∀ b, b ∈ res ↔ a ≠ b ∧ a ≤ b) :=
    fun res_def b => ⟨
      F.leClosure_post_mp res_def b,
      F.leClosure_post_mpr res_def b
    ⟩
end lemma_1_f
