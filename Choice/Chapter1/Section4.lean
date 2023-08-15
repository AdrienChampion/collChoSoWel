import Choice.Chapter1.Section3



/-! # Section 1.4 -/
namespace Choice



section subrelation
  @[simp]
  abbrev Preorder.semiSubrel {S : Set α} (O : Order S) (P : Preorder α) : Prop :=
    ∀ (a b : {x // x ∈ S}), (P.le a b → O.le a b)

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
      let .cons _ _ _ _ _ _ _ _ legit_sub := legit
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
      let .cons _ _ _ _ _ _ h_le_x h_y_le legit_sub := legit
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



  section complement
    structure Preorder.Complement (P : Preorder α) where
      Incmp : Set α
      decMem : ∀ a, Decidable (a ∈ Incmp)
      isIncmp : ∀ a b, a ∈ Incmp → b ∈ Incmp → ¬ a ≤ b ∧ ¬ b ≤ a
      Ord : Order Incmp

    instance {C : P.Complement} {a : α} : Decidable (a ∈ C.Incmp) :=
      C.decMem a

    variable
      (self : P.Complement)

    @[simp]
    abbrev Preorder.Complement.le :=
      self.Ord.le

    abbrev Preorder.Complement.semiSubrel : Preorder α → Prop :=
      Preorder.semiSubrel self.Ord
    
    theorem Preorder.Complement.raw_cons
      {le_x : List α} {x y : self.Incmp} {y_le : List α} {sub : Totalizer.Raw P}
      {legit : (Totalizer.Raw.cons le_x x y y_le sub).Legit}
      (self_x_y : self.le x y)
    : (∀ (a b : self.Incmp), (sub.le a b → self.le a b))
    → ∀ (a b : self.Incmp), (Totalizer.Raw.cons le_x x y y_le sub).le a b → self.le a b
    := by
      let .cons _ _ _ _ _ _ le_a_iff b_le_iff _ := legit
      intro ih a b
      simp [le, le_a_iff, b_le_iff]
      intro h
      cases h with
      | inl h =>
        apply self.Ord.le_trans (ih _ _ h.left)
        apply self.Ord.le_trans self_x_y
        exact ih _ _ h.right
      | inr =>
        apply ih
        assumption
  end complement



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

    abbrev le_a_iff
      [P : Preorder α]
      {sub : Totalizer.Raw P}
      {legit : (@Totalizer.Raw.cons α P le_a a b b_le sub).Legit}
      {x : α}
    : x ∈ le_a ↔ sub.le x a
    := by
      cases legit with | cons _ _ _ _ _ _ le_a_iff _ _ =>
      apply le_a_iff x

    abbrev b_le_iff
      [P : Preorder α]
      {sub : Totalizer.Raw P}
      {legit : (@Totalizer.Raw.cons α P le_a a b b_le sub).Legit}
      {x : α}
    : x ∈ b_le ↔ sub.le b x
    := by
      cases legit with | cons _ _ _ _ _ _ _ b_le_iff _ =>
      apply b_le_iff x
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

    abbrev Preorder.Totalizer.toPreorder (t : P.Totalizer) : Preorder α where
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
    --   t.toPreorder
  end

  theorem Preorder.Totalizer.empty_le
  : ∀ (a b), (empty P).le a b ↔ P.le a b := by
    intro a b
    simp [le]

  def Preorder.Totalizer.empty_subrel
  : P ⊆ (empty P).toPreorder := by
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
    {a : α} {l : List α} {above : Bool}
  : ∀ b ∈ aux self a above l, b ∈ l := by
    induction l with
    | nil =>
      intros
      contradiction
    | cons hd tl ih =>
      intro b
      simp only [aux]
      split
      case inl h =>
        intro b_in_res
        cases b_in_res ; exact List.Mem.head tl
        case tail b_in_sub =>
        let ⟨h_above, _⟩ := h
        simp [aux, h_above]
        · apply Or.inr
          apply ih
          assumption
      case inr h =>
        simp at h
        split
        · intro b_in_res
          cases b_in_res ; exact List.Mem.head tl
          case tail b_in_sub =>
          simp [not_and_or] at h
          apply List.Mem.tail
          apply ih _ b_in_sub
        · intro b_in_res
          apply List.Mem.tail
          apply ih _ b_in_res



  section above
    theorem Preorder.Totalizer.leClosure.aux_above_post_mp
      (self : P.Totalizer)
      {a : α} {l : List α}
    : ∀ b ∈ aux self a true l, self.le a b := by
      induction l with
      | nil =>
        intro b _
        contradiction
      | cons hd tl ih =>
        simp [aux]
        split
        case inl h =>
          intro b b_in_res
          cases b_in_res with
          | head tl => exact h
          | tail hd b_in_tl =>
            exact ih b b_in_tl
        case inr h =>
          exact ih

    theorem Preorder.Totalizer.leClosure.aux_above_post_mpr
      (self : P.Totalizer)
      {a : α} {l : List α}
    : ∀ b ∈ l, self.le a b → b ∈ aux self a true l := by
      induction l with
      | nil =>
        intro b _
        contradiction
      | cons hd tl ih =>
        simp only [aux]
        split
        case inl h =>
          intro b b_in_res
          cases b_in_res with
          | head tl =>
            intro
            exact List.Mem.head _
          | tail hd b_in_tl =>
            intro h
            let b_in_sub := ih b b_in_tl h
            exact List.Mem.tail _ b_in_sub
        case inr h =>
          simp only [not_and_or, false_or] at h
          intro b b_in_l h_b
          simp
          cases b_in_l with
          | head _ => contradiction
          | tail _ h =>
            exact ih b h h_b

    theorem Preorder.Totalizer.leClosure_above_post_mp
      [Finite α]
      (self : P.Totalizer)
      {a : α}
    : ∀ b ∈ self.leClosure a true, self.le a b :=
      leClosure.aux_above_post_mp self

    theorem Preorder.Totalizer.leClosure_above_post_mpr
      [F : Finite α]
      (self : P.Totalizer)
      {a : α}
    : ∀ b, self.le a b → b ∈ self.leClosure a true :=
      fun b h_b =>
        Totalizer.leClosure.aux_above_post_mpr self b (F.all_in_elems b) h_b

    theorem Preorder.Totalizer.leClosure_above_post
      [Finite α]
      (self : P.Totalizer)
      {a : α}
    : ∀ b, b ∈ self.leClosure a true ↔ self.le a b :=
      fun b => ⟨
        self.leClosure_above_post_mp b,
        self.leClosure_above_post_mpr b
      ⟩
  end above



  section below
    theorem Preorder.Totalizer.leClosure.aux_below_post_mp
      (self : P.Totalizer)
      {a : α} {l : List α}
    : ∀ b ∈ aux self a false l, self.le b a := by
      induction l with
      | nil =>
        intro b _
        contradiction
      | cons hd tl ih =>
        simp [aux]
        split
        case inl h =>
          intro b b_in_res
          cases b_in_res with
          | head tl => exact h
          | tail hd b_in_tl =>
            exact ih b b_in_tl
        case inr h =>
          exact ih

    theorem Preorder.Totalizer.leClosure.aux_below_post_mpr
      (self : P.Totalizer)
      {a : α} {l : List α}
    : ∀ b ∈ l, self.le b a → b ∈ aux self a false l := by
      induction l with
      | nil =>
        intro b _
        contradiction
      | cons hd tl ih =>
        simp only [aux]
        split
        case inl h =>
          intro b b_in_res
          cases b_in_res with
          | head tl =>
            intro
            exact List.Mem.head _
          | tail hd b_in_tl =>
            intro h
            let b_in_sub := ih b b_in_tl h
            exact List.Mem.tail _ b_in_sub
        case inr h =>
          intro b b_in_l ba
          cases b_in_l with
          | head _ =>
            simp [true_and, ba]
            split <;> exact List.Mem.head _
          | tail _ h =>
            simp
            split
            <;> try apply List.Mem.tail
            · exact ih b h ba
            · exact ih b h ba

    theorem Preorder.Totalizer.leClosure_below_post_mp
      [Finite α]
      (self : P.Totalizer)
      {a : α}
    : ∀ b ∈ self.leClosure a false, self.le b a :=
      leClosure.aux_below_post_mp self

    theorem Preorder.Totalizer.leClosure_below_post_mpr
      [F : Finite α]
      (self : P.Totalizer)
      {a : α}
    : (∀ b, self.le b a → b ∈ self.leClosure a false) :=
      fun b h_b =>
        Preorder.Totalizer.leClosure.aux_below_post_mpr self b (F.all_in_elems b) h_b

    theorem Preorder.Totalizer.leClosure_below_post
      [Finite α]
      (self : P.Totalizer)
      {a : α}
    : (∀ b, b ∈ self.leClosure a false ↔ self.le b a) :=
      fun b => ⟨
        self.leClosure_below_post_mp b,
        self.leClosure_below_post_mpr b
      ⟩
  end below


  def Preorder.Totalizer.Raw.Legit.for_cons
    [Finite α]
    {P : Preorder α}
    {self : P.Totalizer}
    {not_x_y : ¬ self.le x y}
  : (Raw.cons
      (self.leClosure x false)
      x y
      (self.leClosure y true) 
      self.raw
    ).Legit
  := by
    apply Legit.cons
    <;> try assumption
    · exact leClosure_below_post (α := α) _
    · exact leClosure_above_post (α := α) _
    · exact self.legit



  def Preorder.Totalizer.add
    [F : Finite α]
    (self : P.Totalizer)
    (a b : α)
    (incmp : ¬ self.le a b ∧ ¬ self.le b a)
    (both : Bool := false)
  : P.Totalizer :=
    let ⟨incmp_lft, incmp_rgt⟩ := incmp
    let le_a := self.leClosure a false
    let b_le := self.leClosure b true
    let h_le_a :=
      self.leClosure_below_post (a := a)
    let h_b_le :=
      self.leClosure_above_post (a := b)

    let raw' :=
      Raw.cons le_a a b b_le self.raw
    let raw_legit' :=
      Raw.Legit.cons le_a a b b_le self.raw incmp_lft h_le_a h_b_le self.legit
    let self' :=
      Totalizer.mk raw' raw_legit'

    if ¬ both then
      self'
    else
      let le_b := self'.leClosure b false
      let a_le := self'.leClosure a true
      let h_le_b :=
        self'.leClosure_below_post
      let h_a_le :=
        self'.leClosure_above_post

      let incmp_rgt' : ¬ self'.le b a := by
        simp [le]
        intro h
        cases h with
        | inl h =>
          apply incmp_rgt
          apply h_le_a b |>.mp
          exact h.left
        | inr h =>
          apply incmp_rgt
          exact h
      by
        apply mk $ .cons le_b b a a_le raw'
        apply Raw.Legit.cons <;> try assumption

  theorem Preorder.Totalizer.add_subrel
    [F : Finite α]
    {self : P.Totalizer}
    {x y : α}
    {incmp' : ¬ self.le x y ∧ ¬ self.le y x}
    (both : Bool)
  : self.toPreorder ⊆ (self.add x y incmp' both).toPreorder := by
    intro a b
    simp [LT.lt, LE.le, le, Raw.leB]
    apply And.intro
    · intro h
      simp [add]
      split ; split
      case left.inl incmp_xy incmp_yx h_both =>
        simp
        apply Or.inr $ Or.inr h
      case left.inr incmp_xy incmp_yx h_both =>
        simp
        apply Or.inr h
    · rw [Bool.eq_false_iff, Bool.eq_false_iff]
      intro ab not_ba
      simp [add]
      -- let .cons _ _ _ _ := self.add x y incmp' both |>.legit
      split ; split
      case right.inl incmp_lft incmp_rgt _ =>
        simp [Raw.leB, Bool.eq_false_iff]
        intro h
        cases h with
        | inl h =>
          let h_by :=
            leClosure_below_post_mp _ b h.left
          let h_xa :=
            leClosure_above_post_mp _ a h.right
          simp [le] at h_by
          simp [le] at h_xa
          cases h_by <;> cases h_xa
          case inl.inl h_bx h_ya =>
            apply incmp_rgt
            let bx := self.leClosure_below_post_mp b h_bx.left
            let ya := self.leClosure_above_post_mp a h_ya.right
            apply self.le_trans y a x ya
            apply self.le_trans a b x ab bx
          case inl.inr h_bx xa =>
            apply not_ba
            let bx := self.leClosure_below_post_mp b h_bx.left
            apply self.le_trans b x a bx xa
          case inr.inl b_le_y h_ya =>
            apply not_ba
            let ya := self.leClosure_above_post_mp a h_ya.right
            apply self.le_trans b y a b_le_y ya
          case inr.inr b_le_y x_le_a =>
            apply incmp_lft
            apply self.le_trans x a y x_le_a
            apply self.le_trans a b y ab b_le_y
        | inr h => cases h with
        | inl h =>
          apply incmp_rgt
          let bx :=
            self.leClosure_below_post_mp b h.left
          let ya :=
            self.leClosure_above_post_mp a h.right
          apply self.le_trans y a x ya
          apply self.le_trans a b x ab bx
        | inr h =>
          contradiction
      case right.inr incmp_lft incmp_rgt _ =>
        simp [Bool.eq_false_iff]
        intro h
        cases h
        case inl h =>
          apply incmp_rgt
          let bx :=
            self.leClosure_below_post_mp b h.left
          let ya :=
            self.leClosure_above_post_mp a h.right
          apply self.le_trans y a x ya
          apply self.le_trans a b x ab bx
        case inr h =>
          contradiction



  theorem Preorder.Totalizer.add_post
    [F : Finite α]
    {self : P.Totalizer}
    {a b : α}
    {incmp : ¬ self.le a b ∧ ¬ self.le b a}
    {both : Bool}
  : self.add a b incmp both |>.le a b := by
    let _ : a ∈ self.leClosure a false :=
      let h_le_a :=
        self.leClosure_below_post
      h_le_a a |>.mpr (self.le_refl a)
    let _ : b ∈ self.leClosure b true :=
      let h_b_le :=
        self.leClosure_above_post
      h_b_le b |>.mpr (self.le_refl b)
    cases self with | mk raw raw_legit =>
    simp [add]
    split ; case mk incmp_lft incmp_rgt =>
    split
    case inl _ =>
      simp [le]
      apply Or.inr
      apply Or.inl
      apply And.intro
      · assumption
      · assumption
    case inr _ =>
      simp [le]
      apply Or.inl
      apply And.intro
      · assumption
      · assumption



  theorem Preorder.Totalizer.add_both_post
    [F : Finite α]
    {self : P.Totalizer}
    {a b : α}
    {incmp : ¬ self.le a b ∧ ¬ self.le b a}
  : self.add a b incmp true |>.le b a := by
    let _ : a ∈ self.leClosure a false :=
      let h_le_a :=
        self.leClosure_below_post
      h_le_a a |>.mpr (self.le_refl a)
    let _ : b ∈ self.leClosure b true :=
      let h_b_le :=
        self.leClosure_above_post
      h_b_le b |>.mpr (self.le_refl b)
    cases self with | mk raw raw_legit =>
    simp [add]
    split ; case mk incmp_lft incmp_rgt =>
    simp [le]
    rw [leClosure_below_post, leClosure_above_post]
    simp
    rw [leClosure_below_post, leClosure_above_post]
    rw [leClosure_below_post, leClosure_above_post]
    simp [incmp_rgt]
    apply Or.inl
    apply And.intro (raw.le_refl raw_legit b) (raw.le_refl raw_legit a)



  def Preorder.Totalizer.addCmpl
    [F : Finite α]
    (self : P.Totalizer)
    (C : P.Complement)
    (a b : C.Incmp)
    (incmp : ¬ self.le a b ∧ ¬ self.le b a)
  : P.Totalizer :=
    if h_ab : C.le a b then
      if C.le b a then
        self.add a b incmp true
      else
        self.add a b incmp false
    else if h_ba : C.le b a then
      self.add b a incmp.symm false
    else by
      exfalso
      cases C.Ord.le_total a b
      <;> contradiction
    
  def Preorder.Totalizer.addCmpl_subrel
    [F : Finite α]
    {self : P.Totalizer}
    {C : P.Complement}
    {x y : C.Incmp}
    {incmp : ¬ self.le x y ∧ ¬ self.le y x}
  : self.toPreorder ⊆ (self.addCmpl C x y incmp).toPreorder := by
    simp [addCmpl]
    split <;> split <;> try apply add_subrel
    exfalso
    cases C.Ord.le_total x y
    <;> contradiction

  def Preorder.Totalizer.addCmpl_semiSubrel
    [F : Finite α]
    {self : P.Totalizer}
    {C : P.Complement}
    {x y : C.Incmp}
    {incmp : ¬ self.le x y ∧ ¬ self.le y x}
  : C.semiSubrel self.toPreorder
  → C.semiSubrel (self.addCmpl C x y incmp).toPreorder := by
    intro ih
    intro a b
    simp [LE.le, addCmpl]
    split <;> split <;> try contradiction
    case inl.inl x_y y_x =>
      simp [add]
      split
      simp [le, leClosure_below_post, leClosure_above_post]
      intro h ; cases h
      case inl h =>
        let ⟨h₁, h₂⟩ := h
        cases h₁ <;> cases h₂
        case inl.inl h₁ h₂ =>
          let h₁ := ih _ _ h₁.left
          let h₂ := ih _ _ h₂.right
          apply C.Ord.le_trans h₁
          apply C.Ord.le_trans x_y h₂
        case inl.inr h₁ h₂ =>
          let h₁ := ih _ _ h₁.left
          let h₂ := ih _ _ h₂
          apply C.Ord.le_trans h₁ h₂
        case inr.inl h₁ h₂ =>
          let h₁ := ih _ _ h₁
          let h₂ := ih _ _ h₂.right
          apply C.Ord.le_trans h₁ h₂
        case inr.inr h₁ h₂ =>
          let h₁ := ih _ _ h₁
          let h₂ := ih _ _ h₂
          apply C.Ord.le_trans h₁
          apply C.Ord.le_trans y_x h₂
      case inr h =>
        cases h with
        | inl h =>
          let h₁ := ih _ _ h.left
          let h₂ := ih _ _ h.right
          apply C.Ord.le_trans h₁
          apply C.Ord.le_trans x_y h₂
        | inr h =>
          exact ih _ _ h
    case inl.inr x_y not_y_x =>
      simp [add]
      split
      simp [le, leClosure_below_post, leClosure_above_post]
      intro h
      cases h with
      | inl h =>
        let h₁ := ih _ _ h.left
        let h₂ := ih _ _ h.right
        apply C.Ord.le_trans h₁
        apply C.Ord.le_trans x_y h₂
      | inr h =>
        exact ih _ _ h
    case inr.inl not_x_y y_x =>
      simp [add]
      split
      simp [le, leClosure_below_post, leClosure_above_post]
      intro h ; cases h with
      | inl h =>
        let h₁ := ih _ _ h.left
        let h₂ := ih _ _ h.right
        apply C.Ord.le_trans h₁
        apply C.Ord.le_trans y_x h₂
      | inr h =>
        exact ih _ _ h
    
  def Preorder.Totalizer.addCmpl_post
    [F : Finite α]
    {self : P.Totalizer}
    {C : P.Complement}
    {x y : C.Incmp}
    {incmp : ¬ self.le x y ∧ ¬ self.le y x}
  : (C.le x y → (self.addCmpl C x y incmp |>.le x y))
  ∧ (C.le y x → (self.addCmpl C x y incmp |>.le y x)) := by
    simp [addCmpl]
    split <;> split
    case inl.inl x_y y_x =>
      simp [x_y, y_x]
      apply And.intro self.add_post self.add_both_post
    case inl.inr x_y not_y_x =>
      simp [x_y, not_y_x]
      apply self.add_post
    case inr.inl not_x_y y_x =>
      simp [not_x_y, y_x]
      apply self.add_post
    case inr.inr not_x_y not_y_x =>
      simp [not_x_y, not_y_x]




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
    : self.toPreorder ⊆ (aux a' self elems).toPreorder := by
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
            self.add_subrel (x := a') (y := hd) (incmp' := h) false a b
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
    : self.toPreorder ⊆ (self.addFor a').toPreorder := by
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



  def Preorder.Totalizer.addForCmpl
    [F : Finite α]
    (self : P.Totalizer)
    (C : P.Complement)
    (a : C.Incmp)
  : P.Totalizer :=
    aux self F.elems
  where aux self : List α → P.Totalizer
    | b::rest =>
      if incmp : ¬ self.le a b ∧ ¬ self.le b a then
        if h_b : b ∈ C.Incmp then
          aux (self.addCmpl C a ⟨b, h_b⟩ incmp) rest
        else
          aux self rest
      else
        aux self rest
    | [] => self

  theorem Preorder.Totalizer.addForCmpl.aux_subrel
    [F : Finite α]
    {self : P.Totalizer}
    {C : P.Complement}
    {x : C.Incmp}
    {elems : List α}
  : self.toPreorder ⊆ (addForCmpl.aux C x self elems).toPreorder := by
    induction elems generalizing self <;> try simp [aux, subrel_refl]
    case cons hd tl ih =>
    simp [aux]
    split <;> try exact ih
    split
    · apply subrel_trans self.addCmpl_subrel ih
    · exact ih

  theorem Preorder.Totalizer.addForCmpl.aux_semiSubrel
    [F : Finite α]
    {self : P.Totalizer}
    {C : P.Complement}
    {x : C.Incmp}
    {elems : List α}
  : C.semiSubrel self.toPreorder
  → C.semiSubrel (addForCmpl.aux C x self elems).toPreorder := by
    intro h
    induction elems generalizing self <;> try assumption
    case cons hd tl ih =>
    simp [addForCmpl.aux]
    split ; split
    <;> apply ih
    <;> try assumption
    · apply addCmpl_semiSubrel h
    · apply ih
      assumption

  theorem Preorder.Totalizer.addForCmpl.subrel
    [_F : Finite α]
    {self : P.Totalizer}
    {C : P.Complement}
    {x : C.Incmp}
  : self.toPreorder ⊆ (self.addForCmpl C x).toPreorder :=
    addForCmpl.aux_subrel

  theorem Preorder.Totalizer.addForCmpl_semiSubrel
    [_F : Finite α]
    {self : P.Totalizer}
    {C : P.Complement}
    {x : C.Incmp}
  : C.semiSubrel self.toPreorder
  → C.semiSubrel (self.addForCmpl C x).toPreorder :=
    addForCmpl.aux_semiSubrel
    



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
  : self.toPreorder ⊆ (addMissing.aux self elems).toPreorder := by
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
  : self.toPreorder ⊆ self.addMissing.toPreorder :=
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
  : P ⊆ P.totalize.toPreorder := by
    simp [totalize]
    apply Preorder.subrel_trans (b := Totalizer.empty P |>.toPreorder)
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
    P ⊆ T.toPreorder
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

  -- def Preorder.mergeSubTotal
  --   [F : Finite α]
  --   {S : Set α}
  --   [∀ a, Decidable (a ∈ S)]
  --   (P : Preorder α)
  --   (T : Order S)
  --   (h_P : ∀ (a b : α), (h_a : a ∈ S) → (h_b : b ∈ S) → P.le a b → a = b)
  -- : Preorder α :=
  --   let t := Preorder.Totalizer.empty P
  --   allPairs t F.elems |>.toPreorder
  -- where
  --   allPairs t
  --   | [] => t
  --   | a::tl =>
  --     if S_a : a ∈ S then
  --       allPairs (allElems t a S_a F.elems) tl
  --     else
  --       allPairs t tl
  --   allElems t a S_a
  --   | [] => t
  --   | b::tl =>
  --     if h_ne : a = b then
  --       t
  --     else if S_b : b ∈ S then
  --       if not_ab : ¬ t.le a b then
  --         if T_ab : T.le ⟨a, S_a⟩ ⟨b, S_b⟩ then
  --           allElems
  --             (t.add a b (by
  --               apply And.intro not_ab
  --               · intro ab
  --                 apply h_ne
  --                 apply h_P a b S_a S_b
  --                 simp at h
  --                 apply h
  --                 apply T_ab
  --                 simp [LE.le]
  --             ))
  --             a
  --             S_a
  --             tl
  --         else
  --           allElems t a S_a tl
  --       else
  --         sorry
  --     else
  --       sorry

  -- theorem lemma_1_g
  --   (S : Set α)
  --   (P : Preorder α)
  --   (h_P : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a = b)
  --   (T : Order {a // a ∈ S})
  -- : ∃ (R : Preorder α), 
end lemma_1_g
