import Choice.Chapter1.Section3



/-! # Section 1.4 -/
namespace Choice



section subrelation
  @[simp]
  abbrev Preorder.semiSubrel {S : Set α} (O : Order S) (P : Preorder α) : Prop :=
    ∀ (a b : {x // x ∈ S}), P.le a b → O.le a b
  @[simp]
  abbrev Preorder.semiSubrel' {S : Set α} (O : Order S) (P : Preorder α) : Prop :=
    ∀ (a b : {x // x ∈ S}), P.le a b → ¬ O.le b a → ¬ P.le b a

  @[simp]
  abbrev Order.subrel {S: Set α} (O : Order S) (P : Preorder α) : Prop :=
    ∀ (a b : S), O.le a b → (P.le a b ∧ (¬ O.le b a → ¬ P.le b a))

  /-- Definition 1*5, sub-relation, noted `R₁ ⊆ R₂`. -/
  abbrev Preorder.subrel (P₁ P₂ : Preorder α) : Prop :=
    ∀ a b, P₁.le a b → (P₂.le a b ∧ (¬ P₁.le b a → ¬ P₂.le b a))

  instance instHasSubsetPreorder (α : Type u) : HasSubset (Preorder α) where
    Subset R₁ R₂ := R₁.subrel R₂
  
  theorem Preorder.subrel_refl (P : Preorder α) : P ⊆ P :=
    fun a b => by simp [P.lt_def]

  theorem Preorder.subrel_trans
    {a b c : Preorder α}
  : a ⊆ b → b ⊆ c → a ⊆ c := by
    intro h₁₂ h₂₃
    simp [Subset, subrel, a.lt_def, b.lt_def, c.lt_def] at *
    intro a b a_b
    let h₁₂ := h₁₂ a b a_b
    let h₂₃ := h₂₃ a b
    apply And.intro
    · apply h₂₃ _ |>.left
      apply h₁₂.left
    · intro not_b_a₁ b_a₃
      apply h₂₃ _ |>.right
      · apply h₁₂.right not_b_a₁
      · assumption
      · apply h₁₂.left

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



section
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
      right
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
        left
        apply And.intro
        · apply h_le_x a |>.mpr
          let bx :=
            h_le_x b |>.mp dom_bc.left
          apply ih legit_sub _ _ _ sub_ab bx
        · exact dom_bc.right
      case inl.inr dom_ab sub_bc =>
        left
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
      isIncmp : ∀ a b, a ∈ Incmp → b ∈ Incmp → ¬ P.le a b ∧ ¬ P.le b a
      Ord : Order Incmp

    instance {C : P.Complement} {a : α} : Decidable (a ∈ C.Incmp) :=
      C.decMem a

    variable
      (self : P.Complement)

    @[simp]
    abbrev Preorder.Complement.le :=
      self.Ord.le
    @[simp]
    abbrev Preorder.Complement.le_refl :=
      self.Ord.le_refl
    @[simp]
    abbrev Preorder.Complement.le_trans :=
      self.Ord.le_trans
    
    @[simp]
    abbrev Preorder.Complement.inIncmp : Type u := {x // x ∈ self.Incmp}

    abbrev Preorder.Complement.semiSubrel : Preorder α → Prop :=
      Preorder.semiSubrel self.Ord

    abbrev Preorder.Complement.semiSubrel' : Preorder α → Prop :=
      Preorder.semiSubrel' self.Ord
    
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
    @[simp]
    theorem le_refl' {a} : self.le a a :=
      self.raw.le_refl self.legit a
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
    
    abbrev Preorder.Totalizer.dualSanity₁
      (T : P.Totalizer) (C : P.Complement)
    : Prop :=
      ∀ (a : C.inIncmp) b,
        (not_Incmp_b : b ∉ C.Incmp)
        → T.le a b
        → ∃ (a' : C.inIncmp), T.le a a' ∧ P.le a' b
    
    abbrev Preorder.Totalizer.dualSanity₂
      (T : P.Totalizer) (C : P.Complement)
    : Prop :=
      ∀ a (b : C.inIncmp),
        (not_Incmp_a : a ∉ C.Incmp)
        → T.le a b
        → ∃ (b' : C.inIncmp), P.le a b' ∧ T.le b' b

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
      
    structure Preorder.Totalizer.Sane
      (T : P.Totalizer) (C : P.Complement)
    where
      subrel : P ⊆ T.toPreorder
      ssr : C.semiSubrel T.toPreorder
      ssr' : C.semiSubrel' T.toPreorder
      sanity₁ : T.dualSanity₁ C
      sanity₂ : T.dualSanity₂ C

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
        · right
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

    @[simp]
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

    @[simp]
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



  section addCmpl
    def Preorder.Totalizer.addCmpl
      [_F : Finite α]
      (self : P.Totalizer)
      (C : P.Complement)
      (x y : C.Incmp)
      (incmp : ¬ self.le x y)
    : P.Totalizer :=
      let le_x := self.leClosure x false
      let y_le := self.leClosure y true
      let h_le_x :=
        self.leClosure_below_post (a := x)
      let h_y_le :=
        self.leClosure_above_post (a := y)

      Totalizer.mk
        (Raw.cons le_x x y y_le self.raw)
        (Raw.Legit.cons le_x x y y_le self.raw incmp h_le_x h_y_le self.legit)

    theorem Preorder.Totalizer.addCmpl_semiSubrel
      [F: Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
      (cmpl_x_y : C.le x y)
    : C.semiSubrel self.toPreorder
      → C.semiSubrel (self.addCmpl C x y incmp).toPreorder
    := by
      intro ssr
      intro a b
      simp [LE.le, addCmpl]
      intro h
      cases h with
      | inl h =>
        apply C.le_trans (ssr _ _ h.left)
        apply C.le_trans cmpl_x_y
        exact ssr _ _ h.right
      | inr h =>
        exact ssr _ _ h

    theorem Preorder.Totalizer.addCmpl_semiSubrel'
      [F: Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
      (x_y : C.le x y)
    : C.semiSubrel self.toPreorder
      → C.semiSubrel' (self.addCmpl C x y incmp).toPreorder
    := by
      intro ssr
      intro a b
      simp [LE.le, addCmpl]
      intro _ not_b_a
      intro h
      cases h with
      | inl h =>
        let ⟨self_b_x, self_y_a⟩ := h
        apply not_b_a
        let b_x := ssr _ _ self_b_x
        let y_a := ssr _ _ self_y_a
        apply C.le_trans b_x
        apply C.le_trans x_y y_a
      | inr self_b_a =>
        apply not_b_a
        apply ssr _ _ self_b_a

    theorem Preorder.Totalizer.addCmpl_dualSanity₁
      [F: Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
      (ih : self.dualSanity₁ C)
    : (self.addCmpl C x y incmp).dualSanity₁ C
    := by
      intro a b not_Incmp_b
      simp [LE.le, addCmpl]
      intro h
      cases h
      case inl h =>
        let ⟨self_a_x, self_y_b⟩ := h
        let ⟨y', self_y'_y, P_y_b⟩ := ih y b not_Incmp_b self_y_b
        exists y'
        simp
        apply And.intro _ P_y_b
        left
        apply And.intro self_a_x self_y'_y
      case inr h =>
        let ⟨a', self_a_a', P_a'_b⟩ := ih a b not_Incmp_b h
        exists a'
        simp
        apply And.intro _ P_a'_b
        right
        exact self_a_a'

    theorem Preorder.Totalizer.addCmpl_dualSanity₂
      [F: Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
      (ih : self.dualSanity₂ C)
    : (self.addCmpl C x y incmp).dualSanity₂ C
    := by
      intro a b not_Incmp_a
      simp [LE.le, addCmpl]
      intro h
      cases h
      case inl h =>
        let ⟨self_a_x, self_y_b⟩ := h
        let ⟨x', P_a_x', self_x'_x⟩ := ih a x not_Incmp_a self_a_x
        exists x'
        simp
        apply And.intro P_a_x'
        left
        apply And.intro self_x'_x self_y_b
      case inr h =>
        let ⟨b', P_a_b', self_b'_b⟩ := ih a b not_Incmp_a h
        exists b'
        simp
        apply And.intro P_a_b'
        right
        exact self_b'_b

    theorem Preorder.Totalizer.addCmpl_subrel
      [F: Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
      (sanity₁ : self.dualSanity₁ C)
      (sanity₂ : self.dualSanity₂ C)
      (ih : P ⊆ self.toPreorder)
    : P ⊆ (self.addCmpl C x y incmp).toPreorder
    := by
      intro a b
      simp [LE.le, le, addCmpl]
      intro P_a_b
      let self_a_b := ih _ _ P_a_b |>.left
      apply And.intro (Or.inr self_a_b)
      intro P_not_b_a
      let self_not_b_a := -- used in the `try contradiction` below
        ih _ _ P_a_b |>.right P_not_b_a

      intro wrong
      cases wrong <;> try contradiction
      case inl wrong =>
        let ⟨self_b_x, self_y_a⟩ := wrong
        if Incmp_a : a ∈ C.Incmp then
          if Incmp_b : b ∈ C.Incmp then
            let incmp := C.isIncmp a b Incmp_a Incmp_b
            exact incmp.left P_a_b
          else
            let ⟨x', P_b_x', _⟩ := sanity₂ b x Incmp_b self_b_x
            let P_a_x' := P.le_trans P_a_b P_b_x'
            let incmp := C.isIncmp a x' Incmp_a x'.2
            exact incmp.left P_a_x'
        else if Incmp_b : b ∈ C.Incmp then
          let ⟨y', _, P_y'_a⟩ := sanity₁ y a Incmp_a self_y_a
          let P_y'_b := P.le_trans P_y'_a P_a_b
          let incmp := C.isIncmp y' b y'.2 Incmp_b
          exact incmp.left P_y'_b
        else
          let ⟨y', _, P_y'_a⟩ := sanity₁ y a Incmp_a self_y_a
          let ⟨x', P_b_x', _⟩ := sanity₂ b x Incmp_b self_b_x
          let P_y'_x' := P.le_trans P_y'_a (P.le_trans P_a_b P_b_x')
          let incmp := C.isIncmp y' x' y'.2 x'.2
          exact incmp.left P_y'_x'

    theorem Preorder.Totalizer.addCmpl_sane
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
      (cmpl_x_y : C.le x y)
    : self.Sane C → (self.addCmpl C x y incmp).Sane C
    := fun sane =>
      let ⟨subrel, ssr, _ssr', sanity₁, sanity₂⟩ := sane
      ⟨
        self.addCmpl_subrel incmp sanity₁ sanity₂ subrel,
        self.addCmpl_semiSubrel incmp cmpl_x_y ssr,
        self.addCmpl_semiSubrel' incmp cmpl_x_y ssr,
        self.addCmpl_dualSanity₁ incmp sanity₁,
        self.addCmpl_dualSanity₂ incmp sanity₂
      ⟩

    theorem Preorder.Totalizer.addCmpl_impl
      [F: Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
    : ∀ {a b}, self.le a b → (self.addCmpl C x y incmp).le a b
    := by
      intro a b self_a_b
      simp [LE.le, addCmpl]
      right
      exact self_a_b

    theorem Preorder.Totalizer.addCmpl_post
      [F: Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x y : C.Incmp}
      (incmp : ¬ self.le x y)
    : (self.addCmpl C x y incmp).le x y
    := by
      simp [addCmpl]
      left
      apply And.intro self.le_refl' self.le_refl'
  end addCmpl



  section addCmplFor
    def Preorder.Totalizer.addCmplFor
      [F : Finite α]
      (self : P.Totalizer)
      (C : P.Complement)
      (x : C.Incmp)
    : P.Totalizer :=
      aux self F.elems
    where aux self : List α → P.Totalizer
      | [] => self
      | y::rest =>
        if Incmp_y : y ∈ C.Incmp then
          if C.le x ⟨y, Incmp_y⟩ then
            if self_x_y : self.le x y then
              aux self rest
            else
              let self :=
                self.addCmpl C x ⟨y, Incmp_y⟩ self_x_y
              aux self rest
          else
            aux self rest
        else
          aux self rest

    theorem Preorder.Totalizer.addCmplFor.aux_sane
      [F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x : C.Incmp}
      {elems : List α}
    : self.Sane C → (addCmplFor.aux C x self elems).Sane C := by
      intro sane
      induction elems generalizing self <;> simp [aux]
      case nil =>
        exact sane
      case cons y rest ih =>
        if Incmp_y : y ∈ C.Incmp then
          if cmpl_x_y : C.le x ⟨y, Incmp_y⟩ then
            if self_x_y : self.le x y then
              -- `simp [self_x_y]` does not work for some reason `/(T_T)\`
              let h : self.le x y ↔ True :=
                ⟨fun _ => .intro, fun _ => self_x_y⟩
              simp [Incmp_y, cmpl_x_y, h]
              exact ih sane
            else
              -- it works here though `/(T_T)\`
              simp [Incmp_y, cmpl_x_y, self_x_y]
              apply ih
              apply self.addCmpl_sane self_x_y cmpl_x_y sane
          else
            simp [Incmp_y, cmpl_x_y]
            exact ih sane
        else
          simp [Incmp_y]
          exact ih sane

    theorem Preorder.Totalizer.addCmplFor_sane
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x : C.Incmp}
    : self.Sane C → (self.addCmplFor C x).Sane C :=
      addCmplFor.aux_sane

    theorem Preorder.Totalizer.addCmplFor.aux_impl
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x : C.Incmp}
      {elems : List α}
    : ∀ {a b}, self.le a b → (aux C x self elems).le a b := by
      intro a b self_a_b
      induction elems generalizing self <;> simp [aux]
      case nil =>
        exact self_a_b
      case cons y rest ih =>
        if Incmp_y : y ∈ C.Incmp then
          if cmpl_x_y : C.le x ⟨y, Incmp_y⟩ then
            if self_x_y : self.le x y then
              -- `simp [self_x_y]` does not work for some reason `/(T_T)\`
              let h : self.le x y ↔ True :=
                ⟨fun _ => .intro, fun _ => self_x_y⟩
              simp [Incmp_y, cmpl_x_y, h]
              exact ih self_a_b
            else
              -- it works here though `/(T_T)\`
              simp [Incmp_y, cmpl_x_y, self_x_y]
              apply ih
              apply addCmpl_impl
              assumption
          else
            simp [Incmp_y, cmpl_x_y]
            exact ih self_a_b
        else
          simp [Incmp_y]
          exact ih self_a_b

    theorem Preorder.Totalizer.addCmplFor_impl
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x : C.Incmp}
    : ∀ {a b}, self.le a b → (self.addCmplFor C x).le a b :=
      addCmplFor.aux_impl
    
    theorem Preorder.Totalizer.addCmplFor.aux_post
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x : C.Incmp}
      {elems : List α}
    : ∀ (z : C.inIncmp), z.1 ∈ elems → C.le x z → (addCmplFor.aux C x self elems).le x z := by
      intro z z_in_elems cmpl_x_z
      induction elems generalizing self <;> simp [aux]
      case nil =>
        contradiction
      case cons y rest ih =>
      cases z_in_elems with
      | head =>
        simp [z.2, cmpl_x_z]
        if self_x_z : self.le x z then
          -- `simp [self_x_z]` does not work for some reason `/(T_T)\`
          let h : self.le x z ↔ True :=
            ⟨fun _ => .intro, fun _ => self_x_z⟩
          simp [cmpl_x_z, h]
          apply addCmplFor.aux_impl
          assumption
        else
          -- it works here though `/(T_T)\`
          simp [cmpl_x_z, self_x_z]
          apply addCmplFor.aux_impl
          apply addCmpl_post
      | tail =>
        if Incmp_y : y ∈ C.Incmp then
          if cmpl_x_y : C.le x ⟨y, Incmp_y⟩ then
            if self_x_y : self.le x y then
              -- `simp [self_x_y]` does not work for some reason `/(T_T)\`
              let h : self.le x y ↔ True :=
                ⟨fun _ => .intro, fun _ => self_x_y⟩
              simp [Incmp_y, cmpl_x_y, h]
              apply ih
              assumption
            else
              -- it works here though `/(T_T)\`
              simp [Incmp_y, cmpl_x_y, self_x_y]
              apply ih
              assumption
          else
            simp [Incmp_y, cmpl_x_y]
            apply ih
            assumption
        else
          simp [Incmp_y]
          apply ih
          assumption
    
    theorem Preorder.Totalizer.addCmplFor_post
      [F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {x : C.Incmp}
    : ∀ (z : C.inIncmp), C.le x z → (self.addCmplFor C x).le x z :=
      fun z =>
        addCmplFor.aux_post z (F.all_in_elems z)
  end addCmplFor



  section addMissingCmpl
    def Preorder.Totalizer.addMissingCmpl
      [F : Finite α]
      (self : P.Totalizer)
      (C : P.Complement)
    : P.Totalizer :=
      aux self F.elems
    where aux self : List α → P.Totalizer
      | [] => self
      | x::rest =>
        if Incmp_x : x ∈ C.Incmp then
          let self :=
            self.addCmplFor C ⟨x, Incmp_x⟩
          aux self rest
        else
          aux self rest

    theorem Preorder.Totalizer.addMissingCmpl.aux_sane
      [F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {elems : List α}
    : self.Sane C → (addMissingCmpl.aux C self elems).Sane C := by
      intro sane
      induction elems generalizing self <;> simp [aux]
      case nil =>
        exact sane
      case cons x rest ih =>
        if Incmp_x : x ∈ C.Incmp then
          simp [Incmp_x]
          apply ih
          apply self.addCmplFor_sane sane
        else
          simp [Incmp_x]
          exact ih sane

    theorem Preorder.Totalizer.addMissingCmpl_sane
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
    : self.Sane C → (self.addMissingCmpl C).Sane C :=
      addMissingCmpl.aux_sane

    theorem Preorder.Totalizer.addMissingCmpl.aux_impl
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {elems : List α}
    : ∀ {a b}, self.le a b → (aux C self elems).le a b := by
      intro a b self_a_b
      induction elems generalizing self <;> simp [aux]
      case nil =>
        exact self_a_b
      case cons x rest ih =>
        if Incmp_x : x ∈ C.Incmp then
          simp [Incmp_x]
          apply ih
          apply addCmplFor_impl self_a_b
        else
          simp [Incmp_x]
          exact ih self_a_b

    theorem Preorder.Totalizer.addMissingCmpl_impl
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
    : ∀ {a b}, self.le a b → (self.addMissingCmpl C).le a b :=
      addMissingCmpl.aux_impl
    
    theorem Preorder.Totalizer.addMissingCmpl.aux_post
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {elems : List α}
    : ∀ (z z' : C.inIncmp),
      z.1 ∈ elems → C.le z z' → (addMissingCmpl.aux C self elems).le z z'
    := by
      intro z z' z_in_elems cmpl_z_z'
      induction elems generalizing self <;> simp [aux]
      case nil =>
        contradiction
      case cons x rest ih =>
      cases z_in_elems with
      | head =>
        simp [z.2]
        apply addMissingCmpl.aux_impl
        apply addCmplFor_post
        assumption
      | tail =>
        if Incmp_x : x ∈ C.Incmp then
          simp [Incmp_x]
          apply ih
          assumption
        else
          simp [Incmp_x]
          apply ih
          assumption
    
    theorem Preorder.Totalizer.addMissingCmpl_post
      [F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
    : ∀ (z z' : C.inIncmp), C.le z z' → (self.addMissingCmpl C).le z z' :=
      fun z z' =>
        addMissingCmpl.aux_post z z' (F.all_in_elems z)
  end addMissingCmpl

end
