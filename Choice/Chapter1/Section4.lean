import Choice.Chapter1.Section3



/-! # Section 1.4

Introduces the notions of *"subrelation"*, *"compatibility"* and *"semi-subrelation"*. The latter is
not in Sen's book and relates an `Order` and a `Preorder`. It is actually split in two,
`Preorder.semiSubrel` and `Preorder.semiSubrel'`.

Both will be useful to build an order `O` from a preorder `P` such that `P` is a subrelation of `O`,
and prove it correct. All of this is to prove lemma `1*f`. The process of producing `O` is called
*"totalization"* below.

We also define a notion of `Complement` for a preorder `P`, which is an order over a `S : Set α`.
Complements can guide totalization by specifying relations where `P` does not, meaning `S` must be
such that `∀ (a b : S), P.le a b → a = b`. This lets us prove lemma `1*h`.
-/
namespace Choice



/-! ## Preorder subrelation and semi-subrelation -/
section subrelation
  @[simp]
  abbrev Preorder.semiSubrel {S : Set α} (O : Order S) (P : Preorder α) : Prop :=
    ∀ (a b : {x // x ∈ S}), P.le a b → O.le a b
  @[simp]
  abbrev Preorder.semiSubrel' {S : Set α} (O : Order S) (P : Preorder α) : Prop :=
    ∀ (a b : {x // x ∈ S}), P.le a b → ¬ O.le b a → ¬ P.le b a

  abbrev Order.subrel {S: Set α} (O : Order S) (P : Preorder α) : Prop :=
    ∀ (a b : S), O.le a b → (P.le a b ∧ (¬ O.le b a → ¬ P.le b a))

  /-- Definition 1*5, sub-relation, noted `R₁ ⊆ R₂`. -/
  abbrev ProtoOrder.subrel (P₁ P₂ : ProtoOrder α) : Prop :=
    ∀ a b, P₁.le a b → (P₂.le a b ∧ (¬ P₁.le b a → ¬ P₂.le b a))

  instance instHasSubsetProtoOrder (α : Type u) : HasSubset (ProtoOrder α) where
    Subset P₁ P₂ := P₁.subrel P₂
  
  theorem ProtoOrder.subrel_refl (P : ProtoOrder α) : P ⊆ P :=
    fun a b => by simp [P.lt_def]

  theorem ProtoOrder.subrel_trans
    {a b c : ProtoOrder α}
  : a ⊆ b → b ⊆ c → a ⊆ c := by
    intro h₁₂ h₂₃
    simp [Subset, a.lt_def, b.lt_def, c.lt_def] at *
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

  @[simp]
  abbrev ProtoOrder.subrel_def (P₁ P₂ : ProtoOrder α)
  : P₁ ⊆ P₂ ↔ ∀ a b, P₁.le a b → (P₂.le a b ∧ (¬ P₁.le b a → ¬ P₂.le b a)) :=
    by trivial

  instance instHasSubsetPreorder (α : Type u) : HasSubset (Preorder α) where
    Subset R₁ R₂ := R₁.subrel R₂

  @[simp]
  abbrev Preorder.subrel_def (P₁ P₂ : Preorder α)
  : P₁ ⊆ P₂ ↔ ∀ a b, P₁.le a b → (P₂.le a b ∧ (¬ P₁.le b a → ¬ P₂.le b a)) :=
    by trivial

  instance : IsRefl (ProtoOrder α) (instHasSubsetProtoOrder α).Subset where
    refl := ProtoOrder.subrel_refl
  instance : Trans
    (instHasSubsetProtoOrder α).Subset
    (instHasSubsetProtoOrder α).Subset
    (instHasSubsetProtoOrder α).Subset
  where
    trans := ProtoOrder.subrel_trans

  /-- Definition 1*6, order/pre-order compatibility. -/
  abbrev Order.compatWith (O : Order α) (P : Preorder α) : Prop :=
    P.subrel O
  abbrev Preorder.compat (P : Preorder α) (O : Order α) : Prop :=
    P.subrel O
  abbrev ProtoOrder.compat (P : ProtoOrder α) (O : Order α) : Prop :=
    P.subrel O
end subrelation



/-! ## Totalization -/
section
  variable
    {α : Type u}
    [P : Preorder α]

  /-- This type encodes relations between elements that `P` cannot compare.

  The actual totalizer type is `Preorder.Totalizer` below, which stores a value of this type along
  with a proof that the relations it adds are new and legal using `Preorder.Totalizer.Raw.Legit`.
  -/
  inductive Preorder.Totalizer.Raw (P : Preorder α)
  /-- Initial state of the totalization process, no relation has been added. -/
  | root : Totalizer.Raw P
  /-- Addition of new relations for a pair `(a, b)` incomparable in `P`.

  - `le_a` is the list of all elements `x : α` such that `sub.le x a`, **including** `a`;
  - `le_b` is th elist of all elements `y : α` such that `sub.le b y`, **including** `b`.

  The additional relations encoded by this constructor are all `x ≤ y` with `x ∈ le_a` and `y ∈
  le_b`. Currently, storing `a` and `b` is not necessary and just shows which incomparable pair
  in `sub` served as the starting point for adding all these relations.
  -/
  | cons (le_a : List α) (a b : α) (b_le : List α) (sub : Totalizer.Raw P) : Totalizer.Raw P

  @[simp]
  abbrev Preorder.Totalizer.Raw.leB : Totalizer.Raw P → α → α → Bool
  | root => (· ≤ ·)
  | cons le_a' _ _ b'_le sub => fun a b =>
    (a ∈ le_a' ∧ b ∈ b'_le) ∨ sub.leB a b

  @[simp]
  abbrev Preorder.Totalizer.Raw.le (self : Totalizer.Raw P) : α → α → Prop :=
    (leB self · ·)

  /-- Companion proof-type for `Totalizer.Raw`.

  Encodes the properties we need over the raw totalizer.
  -/
  inductive Preorder.Totalizer.Raw.Legit : Totalizer.Raw P → Prop
  /-- Initial state, no new relations, nothing to prove. -/
  | root : Legit Raw.root
  /-- Properties that a raw totalizer `cons`tructor must verify. -/
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
  : self.Legit → ∀ {a b c}, self.le a b → self.le b c → self.le a c := by
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
          apply ih legit_sub sub_ab bx
        · exact dom_bc.right
      case inl.inr dom_ab sub_bc =>
        left
        apply And.intro
        · exact dom_ab.left
        · apply h_y_le c |>.mpr
          let yb :=
            h_y_le b |>.mp dom_ab.right
          apply ih legit_sub yb sub_bc
      case inr.inr sub_ab sub_bc =>
        exact ih legit_sub sub_ab sub_bc |> Or.inr
    
  /-- Extends a preorder over `S : Set α` to a preorder over `α` by adding `a ≤ a` for `a ∉ S`.

  This is going to be useful to express that a `Complement S` is a subrelation of an `Order α`.
  Since a complement only deals with elements in `S : Set α`, we need to extend it to obtain a
  `Preorder α` which we is the actual subrelation of the `Order α`.

  TODO: optimize the proofs in here it's terrible.
  -/
  abbrev Preorder.extended
    {S : Set α}
    [decMemS : ∀ a, Decidable (a ∈ S)]
    [decEq : DecidableEq α]
    (P : Preorder S)
  : Preorder α :=
    let le a b :=
      let _ := decMemS
      if a = b then
        True
      else
        if a_in_S : a ∈ S then
          if b_in_S : b ∈ S then
            P.le ⟨a, a_in_S⟩ ⟨b, b_in_S⟩
          else
            False
        else
          False
    {
      le,
      toDecidableRel := fun a b => by
        let _ := P.toDecidableEq
        simp [LE.le]
        if a_eq_b : a = b then
          simp [a_eq_b]
          exact isTrue True.intro
        else if a_in_S : a ∈ S then
          if b_in_S : b ∈ S then
            simp [a_eq_b, a_in_S, b_in_S]
            apply P.toDecidableRel
          else
            simp [a_eq_b, a_in_S, b_in_S]
            apply isFalse
            trivial
        else
          simp [a_eq_b, a_in_S]
          apply isFalse
          trivial
      toDecidableEq :=
        decEq,
      le_refl' := fun a => by
        simp [LE.le]
      le_trans' := by
        intro a b c
        simp [LE.le]
        split <;> try simp [*]
        · split <;> try simp [*]
          split <;> try simp [*]
          split <;> try simp [*]
          split <;> try simp [*]
          split <;> try simp [*]
          · rename b = c => b_eq_c
            rename ¬ c ∈ S => c_in_Incmp
            rw [← b_eq_c] at c_in_Incmp
            contradiction
          · split <;> try simp [*]
            split <;> try simp [*]
            exact fun h h' => P.le_trans h h'
    : Preorder α}

  theorem Preorder.extended_post_S
    {S : Set α}
    [decMemS : ∀ a, Decidable (a ∈ S)]
    [decEq : DecidableEq α]
    {P : Preorder S}
  : ∀ {a b : S},
    P.extended.le a b ↔ P.le a b
  := fun {a b} => by
    simp [LE.le]
    split <;> simp [LE.le]
    case inl h =>
    rw [Subtype.ext h]
    apply P.le_refl

  theorem Preorder.extended_post_not_S
    {S : Set α}
    [decMemS : ∀ a, Decidable (a ∈ S)]
    [decEq : DecidableEq α]
    {P : Preorder S}
  : ∀ {a b},
    (a ∉ S ∨ b ∉ S)
    → (P.extended.le a b ↔ a = b)
  := fun {a b} => by
    intro disj
    cases disj
    <;> (simp [LE.le] ; simp [*] ; constructor)
    <;> (try intro ; simp [*])
    <;> (
      intro h
      split at h
      <;> try assumption
    )
    <;> contradiction

  theorem Preorder.extended_post
    {S : Set α}
    [decMemS : ∀ a, Decidable (a ∈ S)]
    [decEq : DecidableEq α]
    {P : Preorder S}
  : ∀ (a b),
    P.extended.le a b ↔ (
      if h : a ∈ S ∧ b ∈ S
      then P.le ⟨a, h.left⟩ ⟨b, h.right⟩
      else a = b
    )
  := fun {a b} => by
    split
    case inl h =>
      apply P.extended_post_S (a := ⟨a, h.left⟩) (b := ⟨b, h.right⟩)
    case inr h =>
      simp only [not_and_or] at h
      apply P.extended_post_not_S h

  theorem Preorder.extended_subrel
    {S : Set α}
    [∀ a, Decidable (a ∈ S)]
    [DecidableEq α]
  : ∀ (P₁ P₂ : Preorder S), P₁ ⊆ P₂ → P₁.extended ⊆ P₂.extended := by
    intro P₁ P₂ P₁_sub_P₂ a b P₁_a_b
    constructor
    · let h_P₁ := P₁.extended_post a b
      let h_P₂ := P₂.extended_post a b
      simp [P₁_a_b] at h_P₁
      rw [h_P₂]
      split
      case inl h =>
        simp [LE.le, h] at h_P₁ h_P₂ P₁_a_b
        apply P₁_sub_P₂ ⟨a, h.left⟩ ⟨b, h.right⟩ h_P₁ |>.left
      case inr h =>
        simp [h] at h_P₁
        assumption
    · let h_P₁ := P₁.extended_post b a
      let h_P₂ := P₂.extended_post b a
      rw [h_P₁, h_P₂]
      split
      case inl dom =>
        simp [LE.le, dom] at h_P₁ h_P₂
        split at h_P₁
        case inl h_eq =>
          simp [h_eq]
          intro h _
          apply h
          apply P₁.le_refl'
        case inr not_b_eq_a =>
          simp [LE.le, dom] at P₁_a_b
          split at P₁_a_b
          case inl h =>
            rw [h] at not_b_eq_a
            contradiction
          · apply P₁_sub_P₂ ⟨a, dom.right⟩ ⟨b, dom.left⟩ P₁_a_b |>.right
      case inr h =>
        intro
        assumption



  /-! ### Complement of a preorder -/
  section complement
    /-- An order over some `S : Set α` such that the elements of `S` are incomparable by `P`. -/
    structure Preorder.Complement (P : Preorder α) where
      /-- Set of incomparable elements. -/
      Incmp : Set α
      /-- `Incmp` membership is decidable. -/
      decMem : ∀ a, Decidable (a ∈ Incmp)
      /-- Elements of `Incmp` are incomparable. -/
      isIncmp : ∀ a b, a ∈ Incmp → b ∈ Incmp → (P.le a b ↔ a = b)
      /-- Order over `Incmp`. -/
      Ord : Order Incmp

    def Preorder.Complement.empty (P : Preorder α) : P.Complement where
      Incmp := ∅
      decMem a := by
        apply isFalse
        simp
      isIncmp := by
        simp
      Ord := P.subEmpty

    instance {C : P.Complement} {a : α} : Decidable (a ∈ C.Incmp) :=
      C.decMem a

    variable
      (self : P.Complement)

    @[simp]
    abbrev Preorder.Complement.le :=
      self.Ord.le
    @[simp]
    abbrev Preorder.Complement.le_refl' :=
      self.Ord.le_refl'
    abbrev Preorder.Complement.le_refl (h : a = b) : self.le a b := by
      rw [h]
      exact self.le_refl' b
    @[simp]
    abbrev Preorder.Complement.le_trans' :=
      self.Ord.le_trans'

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
    
    abbrev Preorder.Complement.extended
      [P : Preorder α]
      (self : P.Complement)
    : Preorder α :=
      self.Ord.toPreorder.extended

    theorem Preorder.Complement.extended_post_incmp
      [P : Preorder α]
      {self : P.Complement}
    : ∀ {a b : self.inIncmp},
      self.extended.le a b ↔ self.le a b
    := fun {a b} => by
      simp [LE.le]
      split <;> simp [LE.le]
      case inl h =>
      rw [Subtype.ext h]
      apply self.le_refl'

    theorem Preorder.Complement.extended_post_not_incmp
      [P : Preorder α]
      {self : P.Complement}
    : ∀ {a b},
      (a ∉ self.Incmp ∨ b ∉ self.Incmp)
      → (self.extended.le a b ↔ a = b)
    := fun {a b} => by
      intro disj
      cases disj
      <;> (simp [LE.le] ; simp [*] ; constructor)
      <;> (try intro ; simp [*])
      <;> (
        intro h
        split at h
        <;> try assumption
      )
      <;> contradiction

    theorem Preorder.Complement.extended_post
      [P : Preorder α]
      {self : P.Complement}
    : ∀ {a b},
      self.extended.le a b ↔ (
        if h : a ∈ self.Incmp ∧ b ∈ self.Incmp
        then self.le ⟨a, h.left⟩ ⟨b, h.right⟩
        else a = b
      )
    := fun {a b} => by
      split
      case inl h =>
        apply self.extended_post_incmp (a := ⟨a, h.left⟩) (b := ⟨b, h.right⟩)
      case inr h =>
        simp only [not_and_or] at h
        apply self.extended_post_not_incmp h
  end complement



  /-! ## Preorder totalization proper

  Sen first shows that a preorder can be "totalized" into an order it is a subrelation of, and then
  shows that, in addition, you can specify what happens on incomparable elements by providing what
  we named `Complement`.
  -/

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
    @[simp]
    theorem le_refl {a} : self.le a a :=
      self.raw.le_refl self.legit a
    theorem le_trans : ∀ {a b c}, self.le a b → self.le b c → self.le a c :=
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
      le_refl' _ := t.le_refl
      le_trans' _ _ _ h h' := t.le_trans h h'
      toDecidableRel := t.instDecLETotalizer
      toDecidableEq := inferInstance

    instance [P : Preorder α] : Coe P.Totalizer (Preorder α) where
      coe T := T.toPreorder
      
    structure Preorder.Totalizer.Sane
      (T : P.Totalizer) (C : P.Complement)
    where
      subrel : P ⊆ T
      ssr : C.semiSubrel T
      ssr' : C.semiSubrel' T
      sanity₁ : T.dualSanity₁ C
      sanity₂ : T.dualSanity₂ C


    theorem Preorder.Totalizer.empty_Sane
      (P : Preorder α) (C : P.Complement)
    : Sane (empty P) C := by
      simp [empty]
      constructor
      · simp [ProtoOrder.subrel_def, LE.le]
      · simp [Complement.semiSubrel, LE.le]
        intro a a_in_Incmp b b_in_Incmp P_a_b
        let h := C.isIncmp a b a_in_Incmp b_in_Incmp |>.mp P_a_b
        apply C.le_refl
        apply Subtype.eq
        simp [h]
      · simp [Complement.semiSubrel', LE.le]
        intro a a_in_Incmp b b_in_Incmp P_a_b not_C_b_a
        let h := C.isIncmp a b a_in_Incmp b_in_Incmp |>.mp P_a_b
        exfalso
        apply not_C_b_a
        apply C.le_refl
        apply Subtype.eq
        simp [h]
      · simp [dualSanity₁, LE.le]
        intro a a_in_Incmp b _not_b_in_Incmp P_a_b
        exists a
      · simp [dualSanity₂, LE.le]
        intro a b a_in_Incmp _not_b_in_Incmp P_a_b
        exists b
    
    theorem Preorder.Totalizer.empty_subrel
      (P : Preorder α)
    : P ⊆ (empty P) := by
      simp [empty]
      intro a b
      simp [LE.le]

    theorem Preorder.Totalizer.empty_le_iff
    : ∀ (a b), (empty P).le a b ↔ P.le a b := by
      intro a b
      simp [le]
  end



  /-! ## Computes the `≤`-closure below/above an element -/
  section leClosure
    /-- Computes all the `x : α` such that `a ≤ x` if `above`, and `x ≤ a` `¬above`. -/
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


    theorem Preorder.Totalizer.Raw.Legit.for_cons
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
  end leClosure



  /-! ## Totalize a pair of incomparable elements for a complement -/
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
    : C.semiSubrel self
      → C.semiSubrel (self.addCmpl C x y incmp)
    := by
      intro ssr
      intro a b
      simp [LE.le, addCmpl]
      intro h
      cases h with
      | inl h =>
        apply C.le_trans' (ssr _ _ h.left)
        apply C.le_trans' cmpl_x_y
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
    : C.semiSubrel self
      → C.semiSubrel' (self.addCmpl C x y incmp)
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
        apply C.le_trans' b_x
        apply C.le_trans' x_y y_a
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
      (ih : P ⊆ self)
    : P ⊆ self.addCmpl C x y incmp
    := by
      simp [addCmpl]
      intro a b
      intro P_a_b
      let self_a_b := ih _ _ P_a_b |>.left
      simp [LE.le, le]
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
            let incmp := C.isIncmp a b Incmp_a Incmp_b |>.mp P_a_b
            apply P_not_b_a
            rw [incmp]
          else
            let ⟨x', P_b_x', _⟩ := sanity₂ b x Incmp_b self_b_x
            let P_a_x' := P.le_trans P_a_b P_b_x'
            let incmp := C.isIncmp a x'.1 Incmp_a x'.2 |>.mp P_a_x'
            rw [← incmp] at P_b_x'
            contradiction
        else if Incmp_b : b ∈ C.Incmp then
          let ⟨y', _, P_y'_a⟩ := sanity₁ y a Incmp_a self_y_a
          let P_y'_b := P.le_trans P_y'_a P_a_b
          let incmp := C.isIncmp y'.1 b y'.2 Incmp_b |>.mp P_y'_b
          rw [incmp] at P_y'_a
          contradiction
        else
          let ⟨y', _, P_y'_a⟩ := sanity₁ y a Incmp_a self_y_a
          let ⟨x', P_b_x', _⟩ := sanity₂ b x Incmp_b self_b_x
          let P_y'_x' := P.le_trans P_y'_a (P.le_trans P_a_b P_b_x')
          let incmp := C.isIncmp y'.1 x'.1 y'.2 x'.2 |>.mp P_y'_x'
          rw [incmp] at P_y'_a
          let wrong := P.le_trans P_b_x' P_y'_a
          contradiction

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
      apply And.intro self.le_refl self.le_refl
  end addCmpl



  /-! ## Totalize all incomparable pairs `(a, b)` for some `a` for a complement -/
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



  /-! ## Totalize all incomparable pairs of elements for a complement -/
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


    theorem Preorder.Totalizer.addMissingCmpl_subrel
      [_F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {sane : self.Sane C}
    : P ⊆ self.addMissingCmpl C :=
      let add_sane := self.addMissingCmpl_sane sane
      add_sane.subrel


    theorem Preorder.Totalizer.addMissingCmpl_cmpl_subrel
      [F : Finite α]
      {self : P.Totalizer}
      {C : P.Complement}
      {sane : self.Sane C}
    : C.extended ⊆ self.addMissingCmpl C := by
      let add_sane := self.addMissingCmpl_sane sane
      intro a b
      rw [C.extended_post]
      simp [LE.le]
      split
      case inl h =>
        let a' : C.inIncmp := ⟨a, h.left⟩
        let b' : C.inIncmp := ⟨b, h.right⟩
        simp [h]
        intro cmpl_a_b
        constructor
        · apply self.addMissingCmpl_post a' b' cmpl_a_b
        · split
          case inl b_eq_a =>
            intro
            contradiction
          case inr b_ne_a =>
            intro
            apply add_sane.ssr' ⟨a, h.left⟩ ⟨b, h.right⟩
            · apply self.addMissingCmpl_post
              assumption
            · assumption
      case inr h =>
        intro a_eq_b
        simp only [not_and_or] at h
        cases h <;> (
          simp [*, a_eq_b]
          apply (self.addMissingCmpl C).le_refl
        )
  end addMissingCmpl



  /-! ## Totalize two incomparable elements by adding a `≤`-relation in both direction -/
  section addBoth
    def Preorder.Totalizer.add
      [_F : Finite α]
      (self : P.Totalizer)
      (x y : α)
      (incmp : ¬ self.le x y ∧ ¬ self.le y x)
    : P.Totalizer :=
      let le_x := self.leClosure x false
      let y_le := self.leClosure y true
      let h_le_x :=
        self.leClosure_below_post (a := x)
      let h_y_le :=
        self.leClosure_above_post (a := y)

      let self' :=
        Totalizer.mk
          (Raw.cons le_x x y y_le self.raw)
          (Raw.Legit.cons le_x x y y_le self.raw incmp.left h_le_x h_y_le self.legit)

      let le_y := self'.leClosure y false
      let x_le := self'.leClosure x true
      let h_le_y :=
        self'.leClosure_below_post (a := y)
      let h_x_le :=
        self'.leClosure_above_post (a := x)

      let incmp_rgt : ¬ self'.le y x :=
        by simp [*]

      Totalizer.mk
        (Raw.cons le_y y x x_le self'.raw)
        (Raw.Legit.cons le_y y x x_le self'.raw incmp_rgt h_le_y h_x_le self'.legit)

    theorem Preorder.Totalizer.add_subrel
      [_F : Finite α]
      {self : P.Totalizer}
      {x y : α}
      (incmp : ¬ self.le x y ∧ ¬ self.le y x)
    : self.toPreorder ⊆ self.add x y incmp := by
      simp [add, LE.le]
      simp only [Subset, ProtoOrder.subrel, LE.le, le]
      intro a b self_a_b
      constructor
      · exact Or.inr (Or.inr self_a_b)
      · intro not_self_b_a
        simp [add]
        intro add_x_a
        cases add_x_a
        case inl h =>
          let ⟨h₁, h₂⟩ := h
          cases h₁ <;> cases h₂
          case inl.inl h₁ h₂ =>
            apply incmp.right
            simp [le]
            apply self.le_trans h₂
            apply self.le_trans self_a_b h₁
          case inl.inr h₁ h₂ =>
            let wrong := self.le_trans h₁ h₂
            apply Bool.eq_false_iff.mp not_self_b_a
            assumption
          case inr.inl h₁ h₂ =>
            let wrong := self.le_trans h₁ h₂
            apply Bool.eq_false_iff.mp not_self_b_a
            assumption
          case inr.inr h₁ h₂ =>
            apply incmp.left
            apply self.le_trans h₂
            apply self.le_trans self_a_b h₁
        case inr h =>
          cases h
          case inl h =>
            apply incmp.right
            apply self.le_trans h.right
            apply self.le_trans self_a_b h.left
          case inr h =>
            apply Bool.eq_false_iff.mp not_self_b_a
            assumption

    theorem Preorder.Totalizer.add_post
      [_F : Finite α]
      {self : P.Totalizer}
      {x y : α}
      (incmp : ¬ self.le x y ∧ ¬ self.le y x)
    : (self.add x y incmp).le x y ∧ (self.add x y incmp).le y x := by
      simp [add]
  end addBoth



  /-! ## Totalize all incomparable pairs `(a, b)` given some `a` -/
  section addFor
    def Preorder.Totalizer.addFor
      [F : Finite α]
      (self : P.Totalizer)
      (x : α)
    : P.Totalizer :=
      aux self F.elems
    where aux self : List α → P.Totalizer
      | [] => self
      | y :: rest =>
        if incmp : ¬ self.le x y ∧ ¬ self.le y x then
          let self :=
            self.add x y incmp
          aux self rest
        else
          aux self rest

    theorem Preorder.Totalizer.addFor.aux_subrel
      [F : Finite α]
      {self : P.Totalizer}
      {x : α}
      {elems : List α}
    : self.toPreorder ⊆ aux x self elems := by
      induction elems generalizing self with
      | nil =>
        simp
      | cons y rest ih =>
        dsimp [aux]
        split
        case inl incmp =>
          let h_add := self.add_subrel incmp
          exact ProtoOrder.subrel_trans h_add ih
        case inr h =>
          exact ih

    theorem Preorder.Totalizer.addFor_subrel
      [_F : Finite α]
      {self : P.Totalizer}
      (x : α)
    : self.toPreorder ⊆ self.addFor x :=
      addFor.aux_subrel

    theorem Preorder.Totalizer.addFor.aux_post
      [F : Finite α]
      {self : P.Totalizer}
      {x : α}
      {elems : List α}
    : ∀ b ∈ elems, (aux x self elems).le x b ∨ (aux x self elems).le b x := by
      intro b b_in_elems
      induction elems generalizing self with
      | nil => contradiction
      | cons y rest ih =>
        simp only [aux]
        split
        case inl incmp =>
          cases b_in_elems
          · left
            let h_add := add_post incmp |>.left
            apply aux_subrel x b h_add |>.left
          · apply ih
            assumption
        case inr incmp =>
          simp only [not_and_or, not_not] at incmp
          cases b_in_elems
          · cases incmp
            · left
              apply aux_subrel x b (by assumption) |>.left
            · right
              apply aux_subrel b x (by assumption) |>.left
          · apply ih
            assumption

    theorem Preorder.Totalizer.addFor_post
      [F : Finite α]
      {self : P.Totalizer}
    : ∀ x b, (self.addFor x).le x b ∨ (self.addFor x).le b x := by
      intro x b
      apply addFor.aux_post
      exact F.all_in_elems b
  end addFor



  /-! ## Totalize all incomparable pairs -/
  section addMissing
    def Preorder.Totalizer.addMissing
      [F : Finite α]
      (self : P.Totalizer)
    : P.Totalizer :=
      aux self F.elems
    where aux self : List α → P.Totalizer
      | [] => self
      | x :: rest =>
        aux (self.addFor x) rest

    theorem Preorder.Totalizer.addMissing.aux_subrel
      [F : Finite α]
      {self : P.Totalizer}
      {elems : List α}
    : self.toPreorder ⊆ aux self elems := by
      induction elems generalizing self with
      | nil =>
        simp
      | cons x rest ih =>
        dsimp [aux]
        apply ProtoOrder.subrel_trans (self.addFor_subrel _) ih

    theorem Preorder.Totalizer.addMissing_subrel
      [_F : Finite α]
      {self : P.Totalizer}
    : self.toPreorder ⊆ self.addMissing :=
      addMissing.aux_subrel

    theorem Preorder.Totalizer.addMissing.aux_post
      [F : Finite α]
      {self : P.Totalizer}
      {elems : List α}
    : ∀ a b, a ∈ elems → (aux self elems).le a b ∨ (aux self elems).le b a := by
      intro a b
      intro a_in_elems
      induction elems generalizing self with
      | nil =>
        contradiction
      | cons x rest ih =>
        simp only [aux]
        cases a_in_elems
        · let h_addFor :=
            self.addFor_post a b
          cases h_addFor
          · left
            apply aux_subrel a b (by assumption) |>.left
          · right
            apply aux_subrel b a (by assumption) |>.left
        · apply ih
          assumption

    theorem Preorder.Totalizer.addMissing_post
      [F : Finite α]
      {self : P.Totalizer}
    : ∀ a b, self.addMissing.le a b ∨ self.addMissing.le b a := by
      intro a b
      apply addMissing.aux_post
      exact F.all_in_elems a
  end addMissing



  /-! ## Top-level totalization functions and properties -/
  section top_level
    /-- Top-level totalization, with complement. -/
    def Preorder.totalizeWith
      [F : Finite α]
      (P : Preorder α)
      (C : P.Complement)
    : Order α :=
      let totalized :=
        Totalizer.empty P
        |>.addMissingCmpl C
        |>.addMissing
      {
        toPreorder := totalized.toPreorder,
        le_total' := by
          intro a b
          simp [LE.le]
          apply Totalizer.addMissing_post
      }

    theorem Preorder.totalizeWith_subrel
      [F : Finite α]
      (P : Preorder α)
      (C : P.Complement)
    : P ⊆ P.totalizeWith C := by
      apply ProtoOrder.subrel_trans $ (Totalizer.empty P).addMissingCmpl_subrel (C := C)
      · exact Totalizer.addMissing_subrel
      · exact Totalizer.empty_Sane P C
    
    theorem Preorder.totalizeWith_subrelCmpl
      [F : Finite α]
      (P : Preorder α)
      (C : P.Complement)
    : C.extended ⊆ P.totalizeWith C := by
      let h : C.extended ⊆ (Totalizer.empty P).addMissingCmpl C := by
        apply Totalizer.addMissingCmpl_cmpl_subrel
        exact Totalizer.empty_Sane P C
      apply ProtoOrder.subrel_trans h
      apply Totalizer.addMissing_subrel



    /-- Top-level totalization, without a complement. -/
    def Preorder.totalize
      [F : Finite α]
      (P : Preorder α)
    : Order α :=
      let totalizer :=
        Totalizer.empty P
      let totalized :=
        totalizer.addMissing
      
      {
        toPreorder := totalized.toPreorder,
        le_total' := by
          intro a b
          apply totalizer.addMissing_post
      }
    
    theorem Preorder.totalize_subrel
      [F : Finite α]
      (P : Preorder α)
    : P ⊆ P.totalize := by
      apply ProtoOrder.subrel_trans (Totalizer.empty_subrel P)
      apply Totalizer.addMissing_subrel
  end top_level
end



/-! ## Actual lemmas from the book -/
section lemmas
  theorem lemma_1_f
    [Finite α]
  :
    ∀ (P : Preorder α),
      ∃ (O : Order α), P ⊆ O
  := by
    intro P
    exists P.totalize
    apply P.totalize_subrel



  theorem lemma_1_g
    [Finite α]
  :
    ∀ (P : Preorder α) (C : P.Complement),
      ∃ (O : Order α), P ⊆ O ∧ C.extended ⊆ O
  := by
    intro P C
    exists P.totalizeWith C
    constructor
    · apply P.totalizeWith_subrel
    · apply P.totalizeWith_subrelCmpl



  /-- Compatibility of a preorder with another preorder, noted `P₁ ≈ P₂`. -/
  abbrev Preorder.compatible (P₁ P₂ : Preorder α) : Prop :=
    ∃ (O : Order α), P₁ ⊆ O ∧ P₂ ⊆ O

  instance : HasEquiv (Preorder α) where
    Equiv := Preorder.compatible



  theorem lemma_1_h
    [Finite α]
  : ∀ (P₁ P₂ : Preorder α), P₁ ⊆ P₂ → P₁ ≈ P₂ := by
    intro P₁ P₂ P₁_P₂
    let O := P₂.totalize
    let P₂_O := P₂.totalize_subrel
    exists O
    constructor
    · apply ProtoOrder.subrel_trans P₁_P₂ P₂_O
    · exact P₂_O



  theorem lemma_1_i
    [Finite α]
    (P : Preorder α)
    {S : Set α}
    [∀ a, Decidable (a ∈ S)]
  :
    (∀ x y, x ∈ S → y ∈ S → (P.le x y ↔ x = y))
    → (P' : Preorder S)
    → P ≈ P'.extended
  := by
    intro incmp P'
    let O' := P'.totalize
    let C' :=
      Preorder.Complement.mk S inferInstance incmp O'
    let O := P.totalizeWith C'
    exists O
    constructor
    · apply P.totalizeWith_subrel
    · let C'_O : C'.extended ⊆ O :=
        P.totalizeWith_subrelCmpl C'
      apply ProtoOrder.subrel_trans _ C'_O
      apply Preorder.extended_subrel
      apply P'.totalize_subrel
end lemmas
