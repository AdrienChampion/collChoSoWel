import Choice.Chapter1.Section3



/-! # Section 1.4 -/
namespace Choice



section subrelation
  /-- Definition 1*5, sub-relation, noted `R₁ ⊆ R₂`. -/
  abbrev Preorder.subrel (P₁ P₂ : Preorder α) : Prop :=
    ∀ a b, (P₁.le a b → P₂.le a b) ∧ (P₁.lt a b → ¬ P₂.le b a)

  instance instHasSubsetPreorder (α : Type u) : HasSubset (Preorder α) where
    Subset R₁ R₂ := R₁.subrel R₂
  
  theorem Preorder.subrel_refl (P : Preorder α) : P ⊆ P :=
    fun a b => by simp [P.lt_def]

  theorem Preorder.subrel_trans
    {a b c : Preorder α}
  : a ⊆ b → b ⊆ c → a ⊆ c := by
    intro h₁₂ h₂₃
    simp [Subset, subrel, a.lt_def, b.lt_def, c.lt_def] at *
    intro a b
    let h₁₂ := h₁₂ a b
    let h₂₃ := h₂₃ a b
    apply And.intro
    · intro ab
      apply h₂₃.left
      apply h₁₂.left ab
    · intro ab nba
      apply h₂₃.right
      · apply h₁₂.left ab
      · apply h₁₂.right ab nba

  instance : IsRefl (Preorder α) (instHasSubsetPreorder α).Subset where
    refl := Preorder.subrel_refl
  instance : Trans
    (instHasSubsetPreorder α).Subset
    (instHasSubsetPreorder α).Subset
    (instHasSubsetPreorder α).Subset
  where
    trans := Preorder.subrel_trans

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
  
  inductive Preorder.Totalizer.Raw (P : Preorder α)
  | root : Totalizer.Raw P
  | cons (le_a : List α) (a b : α) (b_le : List α)
    : Totalizer.Raw P → Totalizer.Raw P

  @[simp]
  abbrev Preorder.Totalizer.Raw.leB : Totalizer.Raw P → α → α → Bool
  | root => (· ≤ ·)
  | cons le_a' _ _ b'_le sub => fun a b =>
    (a ∈ le_a' ∧ b ∈ b'_le) ∨ sub.leB a b

  @[simp]
  abbrev Preorder.Totalizer.Raw.le (self : Totalizer.Raw P) : α → α → Prop :=
    (leB self · ·)

  inductive Preorder.Totalizer.Raw.Legit : Totalizer.Raw P → Prop
  | root : Legit Raw.root
  | cons (le_a : List α) (a b : α) (b_le : List α) sub :
    ¬ sub.le a b
    → ¬ sub.le b a
    → (∀ c, c ∈ le_a ↔ sub.le c a)
    → (∀ c, c ∈ b_le ↔ sub.le b c)
    → Legit sub
    → Legit (cons le_a a b b_le sub)
  
  theorem Preorder.Totalizer.Raw.le_refl
    (self : Totalizer.Raw P)
  : self.Legit → ∀ a, self.le a a := by
    induction self with
    | root => simp [le]
    | cons le_a' a' b' b'_le sub ih =>
      intro legit a
      let .cons _ _ _ _ _ _ _ _ _ legit_sub := legit
      simp [le]
      apply Or.inr
      apply ih legit_sub

  theorem Preorder.Totalizer.Raw.le_trans
    (self : Totalizer.Raw P)
  : self.Legit → ∀ a b c, self.le a b → self.le b c → self.le a c := by
    induction self with
    | root =>
      simp [le]
      intro
      apply Trans.trans
    | cons le_x x y y_le sub ih =>
      simp [le]
      intro legit a b c ab bc
      let .cons _ _ _ _ _ _ _ h_le_x h_y_le legit_sub := legit
      cases ab <;> cases bc
      case inl.inl dom_ab dom_bc =>
        apply Or.inl ⟨dom_ab.left, dom_bc.right⟩
      case inr.inl sub_ab dom_bc =>
        apply Or.inl
        apply And.intro
        · apply h_le_x a |>.mpr
          let bx :=
            h_le_x b |>.mp dom_bc.left
          apply ih legit_sub _ _ _ sub_ab bx
        · exact dom_bc.right
      case inl.inr dom_ab sub_bc =>
        apply Or.inl
        apply And.intro
        · exact dom_ab.left
        · apply h_y_le c |>.mpr
          let yb :=
            h_y_le b |>.mp dom_ab.right
          apply ih legit_sub _ _ _ yb sub_bc
      case inr.inr sub_ab sub_bc =>
        exact ih legit_sub _ _ _ sub_ab sub_bc |> Or.inr



  structure Preorder.Totalizer (P : Preorder α) where
    raw : Totalizer.Raw P
    legit : raw.Legit
  
  def Preorder.Totalizer.empty (P : Preorder α) : P.Totalizer where
    raw := .root
    legit := .root

  namespace Preorder.Totalizer
    variable
      (self : Totalizer P)

    abbrev le :=
      self.raw.le
    theorem le_refl : ∀ a, self.le a a :=
      self.raw.le_refl self.legit
    theorem le_trans : ∀ a b c, self.le a b → self.le b c → self.le a c :=
      self.raw.le_trans self.legit
    @[simp]
    abbrev lt a b :=
      self.le a b ∧ ¬ self.le b a
    abbrev equiv a b :=
      self.le a b ∧ self.le b a
  end Preorder.Totalizer

  section
    variable
      [P : Preorder α]

    instance Preorder.Totalizer.instLETotalizer {t : P.Totalizer} : LE α where
      le := t.le
    instance Preorder.Totalizer.instDecLETotalizer {t : P.Totalizer} : DecidableRel t.le :=
      inferInstance

    instance Preorder.Totalizer.instLTTotalizer {t : P.Totalizer} : LT α where
      lt := t.lt
    instance Preorder.Totalizer.instHasEquivTotalizer {t : P.Totalizer} : HasEquiv α where
      Equiv := t.equiv

    abbrev Preorder.Totalizer.instPreorder (t : P.Totalizer) : Preorder α where
      toLE := t.instLETotalizer
      toLT := t.instLTTotalizer
      toHasEquiv := t.instHasEquivTotalizer
      le_refl := t.le_refl
      le_trans := t.le_trans
      lt_def := by
        simp [LT.lt, LE.le]
      equiv_def := by
        simp [HasEquiv.Equiv, LE.le]
      decidableRel := t.instDecLETotalizer
      decidableEq := inferInstance

    -- instance {t : P.Totalizer} : Preorder α :=
    --   t.instPreorder
  end

  theorem Preorder.Totalizer.empty_le
  : ∀ (a b), (empty P).le a b ↔ P.le a b := by
    intro a b
    simp [le]

  def Preorder.Totalizer.empty_subrel
  : P ⊆ (empty P).instPreorder := by
    intro a b
    simp [P.lt_def, LE.le, empty_le]



  def Preorder.Totalizer.leClosure
    (self : P.Totalizer) [F : Finite α] (a : α) (above : Bool)
  : List α :=
    aux F.elems
  where aux : List α → List α
    | [] => []
    | b::rest =>
      if above ∧ self.le a b
      then b :: (aux rest)
      else if ¬ above ∧ self.le b a
      then b :: (aux rest)
      else aux rest

  theorem Preorder.Totalizer.leClosure.aux_in_list
    (self : P.Totalizer)
    {a : α} {l res : List α} {above : Bool}
  : res = aux self a above l → ∀ b ∈ res, b ∈ l := by
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
      else if h_above : above ∧ self.le a hd then
        simp [h_above, le] at res_def
        apply List.Mem.tail
        let sub := aux self a above tl
        let sub_def : sub = aux self a above tl := rfl
        apply aux_in_list self sub_def
        rw [sub_def]
        rw [res_def] at b_in_res
        cases b_in_res <;> try contradiction
        simp only [h_above.left]
        assumption
      else if h_below : ¬ above ∧ self.le hd a then
        simp [h_below, le] at res_def
        apply List.Mem.tail
        let sub := aux self a above tl
        let sub_def : sub = aux self a above tl := rfl
        apply aux_in_list self sub_def
        rw [sub_def]
        rw [res_def] at b_in_res
        cases b_in_res <;> try contradiction
        simp only [h_below.left]
        assumption
      else
        split at res_def <;> try contradiction
        apply List.Mem.tail
        let sub := aux self a above tl
        let sub_def : sub = aux self a above tl := rfl
        apply aux_in_list self sub_def
        rw [sub_def, ← res_def]
        assumption



  section above
    theorem Preorder.Totalizer.leClosure.aux_above_post_mp
      (self : P.Totalizer)
      {a : α} {l res : List α}
    : res = aux self a true l → ∀ b ∈ res, self.le a b := by
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

    theorem Preorder.Totalizer.leClosure.aux_above_post_mpr
      (self : P.Totalizer)
      {a : α} {l res : List α}
    : res = aux self a true l → ∀ b ∈ l, self.le a b → b ∈ res := by
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

    theorem Preorder.Totalizer.leClosure_above_post_mp
      [Finite α]
      (self : P.Totalizer)
      {a : α} {res : List α}
    : res = self.leClosure a true → ∀ b ∈ res, self.le a b :=
      leClosure.aux_above_post_mp self

    theorem Preorder.Totalizer.leClosure_above_post_mpr
      [F : Finite α]
      (self : P.Totalizer)
      {a : α} {res : List α}
    : res = self.leClosure a true → (∀ b, self.le a b → b ∈ res) :=
      fun res_def b h_b =>
        Totalizer.leClosure.aux_above_post_mpr self res_def b (F.all_in_elems b) h_b

    theorem Preorder.Totalizer.leClosure_above_post
      [Finite α]
      (self : P.Totalizer)
      {a : α} {res : List α}
    : res = self.leClosure a true → (∀ b, b ∈ res ↔ self.le a b) :=
      fun res_def b => ⟨
        self.leClosure_above_post_mp res_def b,
        self.leClosure_above_post_mpr res_def b
      ⟩
  end above



  section below
    theorem Preorder.Totalizer.leClosure.aux_below_post_mp
      (self : P.Totalizer)
      {a : α} {l res : List α}
    : res = aux self a false l → ∀ b ∈ res, self.le b a := by
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

    theorem Preorder.Totalizer.leClosure.aux_below_post_mpr
      (self : P.Totalizer)
      {a : α} {l res : List α}
    : res = aux self a false l → ∀ b ∈ l, self.le b a → b ∈ res := by
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

    theorem Preorder.Totalizer.leClosure_below_post_mp
      [Finite α]
      (self : P.Totalizer)
      {a : α} {res : List α}
    : res = self.leClosure a false → ∀ b ∈ res, self.le b a :=
      leClosure.aux_below_post_mp self

    theorem Preorder.Totalizer.leClosure_below_post_mpr
      [F : Finite α]
      (self : P.Totalizer)
      {a : α} {res : List α}
    : res = self.leClosure a false → (∀ b, self.le b a → b ∈ res) :=
      fun res_def b h_b =>
        Preorder.Totalizer.leClosure.aux_below_post_mpr self res_def b (F.all_in_elems b) h_b

    theorem Preorder.Totalizer.leClosure_below_post
      [Finite α]
      (self : P.Totalizer)
      {a : α} {res : List α}
    : res = self.leClosure a false → (∀ b, b ∈ res ↔ self.le b a) :=
      fun res_def b => ⟨
        self.leClosure_below_post_mp res_def b,
        self.leClosure_below_post_mpr res_def b
      ⟩
  end below



  def Preorder.Totalizer.add
    [F : Finite α]
    (self : P.Totalizer)
    (a b : α)
    (incmp : ¬ self.le a b ∧ ¬ self.le b a)
  : P.Totalizer :=
    let le_a := self.leClosure a false
    let b_le := self.leClosure b true
    by
      let _h_le_a :=
        self.leClosure_below_post (res := le_a) rfl
      let _h_b_le :=
        self.leClosure_above_post (res := b_le) rfl
      cases self with | mk raw raw_legit =>
      apply mk $ .cons le_a a b b_le raw
      apply Raw.Legit.cons <;> try assumption
      · exact incmp.left
      · exact incmp.right

  theorem Preorder.Totalizer.add_subrel
    [F : Finite α]
    {self : P.Totalizer}
    {a' b' : α}
    {incmp' : ¬ self.le a' b' ∧ ¬ self.le b' a'}
  : self.instPreorder ⊆ (self.add a' b' incmp').instPreorder := by
    intro a b
    simp [LT.lt, LE.le, le]
    apply And.intro
    · exact Or.inr
    · intro ab not_ba
      intro b_le_a
      cases b_le_a with
      | inl h =>
        let .cons _ _ _ _ _ _ _ iff_le_a' iff_b'_le _ :=
          (self.add a' b' incmp').legit
        let ba' : self.le b a' :=
          iff_le_a' b |>.mp h.left
        let b'a : self.le b' a :=
          iff_b'_le a |>.mp h.right
        let aa' : self.le a a' :=
          self.le_trans _ _ _ ab ba'
        let b'a' : self.le b' a' :=
          self.le_trans _ _ _ b'a aa'
        contradiction
      | inr ba =>
        apply Bool.eq_false_iff.mp not_ba
        assumption

  theorem Preorder.Totalizer.add_post
    [F : Finite α]
    {self : P.Totalizer}
    {a b : α}
    {incmp : ¬ self.le a b ∧ ¬ self.le b a}
  : self.add a b incmp |>.le a b := by
    let _ : a ∈ self.leClosure a false :=
      let h_le_a :=
        self.leClosure_below_post (res := self.leClosure a false) rfl
      h_le_a a |>.mpr (self.le_refl a)
    let _ : b ∈ self.leClosure b true :=
      let h_b_le :=
        self.leClosure_above_post (res := self.leClosure b true) rfl
      h_b_le b |>.mpr (self.le_refl b)
    cases self with | mk raw raw_legit =>
    simp [le]
    apply Or.inl
    apply And.intro <;> assumption



  def Preorder.Totalizer.addFor
    [F : Finite α]
    (self : P.Totalizer)
    (a : α)
  : P.Totalizer :=
    aux self F.elems
  where aux self : List α → P.Totalizer
    | b::rest =>
      if h : ¬ self.le a b ∧ ¬ self.le b a
      then aux (self.add a b h) rest
      else aux self rest
    | [] => self

  section addFor
    theorem Preorder.Totalizer.addFor.aux_subrel
      [F : Finite α]
      {self : P.Totalizer}
      {a' : α} {elems : List α}
    : self.instPreorder ⊆ (aux a' self elems).instPreorder := by
      simp [Subset, subrel, LT.lt, LE.le, lt]
      induction elems generalizing self with
      | nil =>
        intro a b
        simp [aux]
      | cons hd tl ih =>
        intro a b
        simp only [aux]
        split
        case inl h =>
          let ih := ih (self := self.add a' hd h) a b
          let sub :=
            self.add_subrel (a' := a') (b' := hd) (incmp' := h) a b
          apply And.intro
          · intro ab
            apply ih.left
            apply sub.left ab
          · intro ab not_ba
            apply ih.right
            · apply sub.left ab
            · apply Bool.eq_false_iff.mpr
              apply sub.right ⟨ab, Bool.eq_false_iff.mp not_ba⟩
        case inr _ =>
          apply ih

    theorem Preorder.Totalizer.addFor.aux_post
      [F : Finite α]
      {self : P.Totalizer}
      {a : α} {elems : List α}
    : ∀ b ∈ elems,
        (addFor.aux a self elems |>.le a b) ∨ (addFor.aux a self elems |>.le b a)
    := fun b b_in_elems => by
      cases elems with
      | nil =>
        contradiction
      | cons hd tl =>
        simp only [aux]
        split
        case inl h =>
          cases b_in_elems with
          | head _ =>
            apply Or.inl
            apply aux_subrel a b |>.left
            apply add_post
          | tail _ b_in_tl =>
            apply aux_post b b_in_tl
        case inr h =>
          cases b_in_elems with
          | head _ =>
            simp only [not_and_or, not_not] at h
            cases h
            · apply Or.inl
              apply aux_subrel a b |>.left
              assumption
            · apply Or.inr
              apply aux_subrel b a |>.left
              assumption
          | tail _ b_in_tl =>
            apply aux_post b b_in_tl

    theorem Preorder.Totalizer.addFor_subrel
      [F : Finite α]
      {self : P.Totalizer}
      {a' : α}
    : self.instPreorder ⊆ (self.addFor a').instPreorder := by
      apply addFor.aux_subrel

    theorem Preorder.Totalizer.addFor_post
      [F : Finite α]
      {self : P.Totalizer}
      {a : α}
    : ∀ b, (self.addFor a |>.le a b) ∨ (self.addFor a |>.le b a) := by
      intro b
      simp only [addFor]
      apply addFor.aux_post
      exact F.all_in_elems b
  end addFor



  def Preorder.Totalizer.addMissing
    [F : Finite α]
    (self : P.Totalizer)
  : P.Totalizer :=
    aux self F.elems
  where aux self : List α → P.Totalizer
    | a::rest => aux (self.addFor a) rest
    | [] => self

  def Preorder.Totalizer.addMissing.aux_subrel
    [F : Finite α]
    (self : P.Totalizer)
    {elems : List α}
  : self.instPreorder ⊆ (addMissing.aux self elems).instPreorder := by
    induction elems generalizing self with
    | nil => rfl
    | cons hd tl ih =>
      simp [aux]
      let ih := ih (self.addFor hd)
      apply subrel_trans self.addFor_subrel ih

  def Preorder.Totalizer.addMissing.aux_post
    [F : Finite α]
    (self : P.Totalizer)
    {elems : List α}
  : ∀ a ∈ elems,
    ∀ b, (addMissing.aux self elems).le a b ∨ (addMissing.aux self elems).le b a
  := by
    intro a a_in_elems b
    induction elems generalizing self b with
    | nil => contradiction
    | cons hd tl ih =>
      simp [aux]
      cases a_in_elems with
      | head _ =>
        let h := self.addFor_post (a := a) b
        let sub := aux_subrel (self.addFor a) (elems := tl)
        cases h with
        | inl h =>
          apply Or.inl
          exact (sub a b).left h
        | inr h =>
          apply Or.inr
          exact (sub b a).left h
      | tail _ a_in_tl =>
        exact ih (self.addFor hd) a_in_tl b

  def Preorder.Totalizer.addMissing_subrel
    [Finite α]
    (self : P.Totalizer)
  : self.instPreorder ⊆ self.addMissing.instPreorder :=
    addMissing.aux_subrel self

  def Preorder.Totalizer.addMissing_post
    [F : Finite α]
    (self : P.Totalizer)
  : ∀ a b, self.addMissing.le a b ∨ self.addMissing.le b a :=
    fun a b =>
      addMissing.aux_post self a (F.all_in_elems a) b



  def Preorder.totalize
    (P : Preorder α)
    [Finite α]
  : Totalizer P :=
    let root := Totalizer.empty P
    root.addMissing

  theorem Preorder.totalize_subrel
    (P : Preorder α)
    [Finite α]
  : P ⊆ P.totalize.instPreorder := by
    simp [totalize]
    apply Preorder.subrel_trans (b := Totalizer.empty P |>.instPreorder)
    · apply Totalizer.empty_subrel
    · apply (Totalizer.empty P).addMissing_subrel

  theorem Preorder.totalize_total
    (P : Preorder α)
    [Finite α]
  : ∀ a b, P.totalize.le a b ∨ P.totalize.le b a :=
    (Totalizer.empty P).addMissing_post



  theorem lemma_1_f
    (P : Preorder α)
    [Finite α]
  : ∃ (T : P.Totalizer),
    P ⊆ T.instPreorder
    ∧ Total T.le
  := ⟨P.totalize, P.totalize_subrel, P.totalize_total⟩
end lemma_1_f



section lemma_1_g
  /-- Extends a sub-preorder, *i.e.* a preorder on `Set α`. -/
  def Preorder.extended
    {S : Set α}
    [DecidableEq α]
    [∀ a, Decidable (a ∈ S)]
    (P : Preorder S)
  : Preorder α :=
    let le a b :=
      if h : a ∈ S ∧ b ∈ S
      then P.le ⟨a, h.left⟩ ⟨b, h.right⟩
      else a = b
    let le_trans a b c : le a b → le b c → le a c := by
      if h_ab : a ∈ S ∧ b ∈ S then
        simp [h_ab]
        if h_c : c ∈ S then
          simp [h_c]
          apply P.le_trans
        else
          simp [h_c]
          intro _ b_eq_c
          rw [b_eq_c] at h_ab
          let fls := h_c h_ab.right
          contradiction
      else
        simp [h_ab]
        intro a_eq_b
        rw [a_eq_b]
        exact id
    {
      le := le,
      lt := fun a b => le a b ∧ ¬ le b a,
      Equiv := fun a b => le a b ∧ le b a,
      le_refl := fun a => by simp [LE.le]
      le_trans := le_trans
      decidableRel := fun a b => by
        simp [LE.le]
        if h_ab : a ∈ S ∧ b ∈ S then
          simp [h_ab]
          if h : P.le ⟨a, h_ab.left⟩ ⟨b, h_ab.right⟩ then
            apply isTrue h
          else
            apply isFalse h
        else if h : a = b then
          simp [h_ab, h]
          apply isTrue .intro
        else
          simp [h_ab, h]
          apply isFalse
          intro
          contradiction
      decidableEq := inferInstance
      lt_def := by simp [LT.lt]
      equiv_def := by simp [HasEquiv.Equiv]
      : Preorder α
    }

  -- def Preorder.Totalizer.mergeSubTotal
  --   {P : Preorder α}
  --   (self : Totalizer P)

  -- theorem lemma_1_g
  --   (S : Set α)
  --   (P : Preorder α)
  --   (h_P : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a = b)
  --   (T : Order {a // a ∈ S})
  -- : ∃ (R : Preorder α), 
end lemma_1_g
