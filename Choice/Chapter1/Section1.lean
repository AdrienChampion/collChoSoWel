import Choice.Init



/-! # Section 1.1 -/
namespace Choice



/-! ## Proto-Order

A proto-order over some domain `α` is a decidable relation `≤ : α → α → Prop`, where `α`-equality is
decidable. It provides two (decidable) relations:

- `a < b = a ≤ b ∧ ¬ b ≤ a` --- always irreflexive,
- `a ≈ b = a ≤ b ∧ b ≤ a`.
-/
section proto_order
  class ProtoOrder (α : Type u) extends LE α where
    toDecidableRel : DecidableRel toLE.le
    toDecidableEq : DecidableEq α

  namespace ProtoOrder
    variable
      (P : ProtoOrder α)
    
    @[simp]
    abbrev lt (a b : α) : Prop :=
      a ≤ b ∧ ¬ b ≤ a

    @[simp]
    abbrev equiv (a b : α) : Prop :=
      a ≤ b ∧ b ≤ a
  end ProtoOrder

  abbrev ProtoOrder.toLT (P : ProtoOrder α) : LT α where
    lt := P.lt
  instance [P : ProtoOrder α] : LT α :=
    P.toLT
  abbrev ProtoOrder.toHasEquiv (P : ProtoOrder α) : HasEquiv α where
    Equiv := P.equiv
  instance [P : ProtoOrder α] : HasEquiv α :=
    P.toHasEquiv



  section
    variable
      [ProtoOrder α]
      (a b : α)

    /-- `R`elation of weak preference, noted `a ≤ b`. -/
    abbrev R := a ≤ b
    abbrev ProtoOrder.R := @Choice.R

    /-- `P`reference, noted `a < b`. -/
    abbrev P := a < b
    abbrev ProtoOrder.P := @Choice.P

    /-- `I`ndifference, noted `a ≈ b`. -/
    abbrev I := a ≈ b
    abbrev ProtoOrder.I := @Choice.I
  end

  section
    variable (P : ProtoOrder α)

    theorem ProtoOrder.lt_def' : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
      simp [LT.lt]

    theorem ProtoOrder.equiv_def' : ∀ (a b : α), a ≈ b ↔ a ≤ b ∧ b ≤ a := by
      simp [HasEquiv.Equiv]

    abbrev ProtoOrder.lt_def {a b} :=
      P.lt_def' a b

    abbrev ProtoOrder.equiv_def {a b} :=
      P.equiv_def' a b
    
    def ProtoOrder.lt_intro
      {a b : α} (ab : a ≤ b) (nba : ¬ b ≤ a)
    : a < b := by
      simp [P.lt_def]
      exact ⟨ab, nba⟩
    
    def ProtoOrder.equiv_intro
      {a b : α} (ab : a ≤ b) (ba : b ≤ a)
    : a ≈ b := by
      simp [P.equiv_def]
      exact ⟨ab, ba⟩

    def ProtoOrder.not_lt'
      [T : IsTotal α LE.le]
    : ∀ (a b : α), ¬ a < b → b ≤ a := by
      intro a b
      intro nab
      simp only [P.lt_def, not_and_or, not_not] at nab
      cases nab with
      | inl nab =>
        let res := T.total a b
        simp [nab] at res
        assumption
      | inr ab =>
        assumption
    
    def ProtoOrder.not_lt
      [IsTotal α LE.le]
    : ∀ {a b : α}, ¬ a < b → b ≤ a :=
      fun {a b} => P.not_lt' a b

    def ProtoOrder.lt_asymm'
    : ∀ (a b : α), a < b → ¬ b < a := by
      simp [LT.lt]
      intro a b ab _ _
      assumption

    def ProtoOrder.lt_asymm {a b : α} :=
      P.lt_asymm' a b
  end



  /-! Useful instances. -/
  section
    variable
      [P : ProtoOrder α]

    instance : DecidableEq α :=
      P.toDecidableEq

    instance : DecidableRel P.le :=
      P.toDecidableRel

    instance : DecidableRel (@LT.lt α _) := by
      simp [LT.lt]
      exact inferInstance

    instance : DecidableRel (@HasEquiv.Equiv α _) := by
      simp [HasEquiv.Equiv]
      exact inferInstance

    instance instIsIrreflLT : IsIrrefl α LT.lt where
      irrefl a := by
        rw [P.lt_def, not_and_or, not_not]
        cases Decidable.em (a ≤ a)
        <;> simp [*]

    instance instIsReflEquiv [R : IsRefl α LE.le] : IsRefl α HasEquiv.Equiv where
      refl a := by
        simp [P.equiv_def]
        exact R.refl a

    instance instIsSymmEquiv : IsSymm α HasEquiv.Equiv where
      symm a b := by
        simp only [P.equiv_def]
        exact And.symm

    instance instIsTransLT [T : IsTrans α LE.le] : IsTrans α LT.lt where
      trans a b c := by
        simp [P.lt_def]
        intro ab nba bc _ncb
        constructor
        · exact Trans.trans ab bc
        · intro ca
          apply nba
          exact Trans.trans bc ca

    instance instIsTransEquiv [T : IsTrans α LE.le] : IsTrans α HasEquiv.Equiv where
      trans a b c := by
        simp [P.equiv_def]
        intro ab ba bc cb
        constructor
        · exact Trans.trans ab bc
        · exact Trans.trans cb ba
  end
end proto_order



/-! ## Quasi-Transitivity

The book introduces a notion of *"quasi-transitivity"*, which corresponds to transitivity over `<`.
Since `<` is called `P` in the book, this notion is also called *"PP transitivity"*.
-/
section pp_trans
  @[simp]
  abbrev PpTransitive (α : Type u) [L : LT α] :=
    Transitive L.lt

  class IsPpTrans (α : Type u) [LT α] where
    pp_trans : PpTransitive α

  instance [L : LT α] [Pp : IsPpTrans α] : IsTrans α L.lt where
    trans := Pp.pp_trans

  instance [ProtoOrder α] [IsTrans α LE.le] : IsPpTrans α where
    pp_trans := instIsTransLT.trans
end pp_trans



/-! ## PI-Transitivity

Similar to but different from quasi-transitivity, corresponds to `a < b → b ≈ c → a < c`.
-/
section pi_trans
  variable
    (α : Type u) [LT α] [HasEquiv α]

  abbrev PiTransitive : Prop :=
    ∀ (a b c : α), a < b → b ≈ c → a < c

  class IsPiTrans where
    pi_trans : PiTransitive α
end pi_trans

-- instance [P : ProtoOrder α] [IsTrans α LE.le] : IsPiTrans α where
--   pi_trans := by
--     intro a b c
--     rw [P.lt_def, P.lt_def, P.equiv_def]
--     intro h
--     cases h with | intro ab nba =>
--     intro h
--     cases h with | intro bc cb =>
    
--     sorry



section qpreorder
  class QPreorder (α : Type u) extends ProtoOrder α where
    le_refl' : Reflexive le
    pp_trans' : PpTransitive α

  section
    variable (Q : QPreorder α)

    theorem QPreorder.le_refl {a : α} : a ≤ a :=
      Q.le_refl' a
    theorem QPreorder.pp_trans {a b c : α} : a < b → b < c → a < c :=
      Q.pp_trans' (x := a) (y := b) (z := c)
    theorem QPreorder.lt_trans {a b c : α} : a < b → b < c → a < c :=
      Q.pp_trans
  end

  instance : Coe (QPreorder α) (ProtoOrder α) where
    coe Q := Q.toProtoOrder

  instance [Q : QPreorder α] : IsRefl α LE.le :=
    ⟨Q.le_refl'⟩

  instance [Q : QPreorder α] : IsPpTrans α :=
    ⟨Q.pp_trans'⟩
end qpreorder



/-! ## Preorder

A preorder is a proto-order such that `≤` is reflexive and transitive. Logically however, a preorder
is also a quasi-preorder, so it `Coe`-s to `QPreorder` and generates a `QPreorder` instance
automatically.

Note that our custom notion of preorder is compatible with Mathlib's version, which we prove by
generating a `_root_.Preorder` instance below.
-/
section preorder
  class Preorder (α : Type u) extends ProtoOrder α where
    le_refl' : Reflexive le
    le_trans' : Transitive le

  -- only propagate `≤` transitivity, reflexivity will come from the `QPreorder` instance
  instance [P : Preorder α] : IsTrans α LE.le where
    trans := P.le_trans'

  section
    variable (P : Preorder α)

    theorem Preorder.le_refl {a} : P.le a a :=
      P.le_refl' a

    theorem Preorder.le_trans
      {a b c : α}
    : a ≤ b → b ≤ c → a ≤ c :=
      P.le_trans' (x := a) (y := b) (z := c)

    theorem Preorder.lt_trans'
      (a b c : α)
    : a < b → b < c → a < c := by
      simp [P.lt_def]
      intro a_b _not_b_a b_c not_c_b
      apply And.intro (P.le_trans a_b b_c)
      intro c_a
      apply not_c_b
      exact P.le_trans c_a a_b

    theorem Preorder.lt_trans {a b c : α} : a < b → b < c → a < c :=
      P.lt_trans' a b c

    def Preorder.toQPreorder : QPreorder α where
      le_refl' := P.le_refl'
      pp_trans' := P.lt_trans'

    instance : Coe (Preorder α) (QPreorder α) where
      coe P := P.toQPreorder
    instance [P : Preorder α] : QPreorder α :=
      P.toQPreorder
  end



  def Preorder.toMathlibPreorder (P : Preorder α) : _root_.Preorder α where
    toLE := P.toLE
    toLT := P.toLT
    le_refl := P.le_refl'
    le_trans := P.le_trans'
    lt_iff_le_not_le _ _ := P.lt_def

  instance instMathlibPreorderOfPreorder [P : Preorder α] : _root_.Preorder α :=
    P.toMathlibPreorder
end preorder



/-! ## Quasi-Order

A quasi-order is a quasi-preorder where `≤` is total.
-/
section qorder
  class QOrder (α : Type u) extends QPreorder α where
    le_total' : Total le

  instance : Coe (QOrder α) (QPreorder α) where
    coe Q := Q.toQPreorder

  instance [Q : QOrder α] : IsTotal α LE.le where
    total := Q.le_total'
  
  theorem QOrder.le_total (Q : QOrder α) : ∀ {a b : α}, a ≤ b ∨ b ≤ a :=
    @QOrder.le_total' α Q
end qorder



/-! ## Order

An order is a preorder where `≤` is total. Logically however, an order is also a quasi-order, so it
`Coe`-s to `QOrder` and generates a `QOrder` instance automatically. `Order` still `Coe`-s to
`Preorder` though, because `QOrder` does not imply `Preorder`.
-/
section order
  class Order (α : Type u) extends Preorder α where
    le_total' : Total le
  
  instance [O : Order α] : IsTotal α O.le where
    total := O.le_total'

  def Order.le_total (O : Order α) : ∀ {a b : α}, a ≤ b ∨ b ≤ a :=
    @Order.le_total' α O

  theorem Order.le_subst (O O' : Order α) (h : O = O') : O.le x y → O'.le x y := by
    cases h
    intro
    assumption

  theorem Order.lt_subst (O O' : Order α) (h : O = O') : O.lt x y → O'.lt x y := by
    cases h
    intro
    assumption

  def Order.toQOrder (O : Order α) : QOrder α where
    toQPreorder := O.toPreorder.toQPreorder
    le_total' := O.le_total'

  instance : Coe (Order α) (QOrder α) where
    coe O := O.toQOrder
  instance : Coe (Order α) (Preorder α) where
    coe O := O.toPreorder
  instance : Coe (Order α) (ProtoOrder α) where
    coe O := O.toPreorder
  
  instance [O : Order α] : QOrder α :=
    O.toQOrder
end order



/-! ## Partial Order

A partial order is a preorder where `≤` is antisymmetric.

Note that our custom notion of partial order is compatible with Mathlib's version, which we prove by
generating a `_root_.PartialOrder` instance below.
-/
section partial_order
  class PartialOrder (α : Type u) extends Preorder α where
    toIsAntisymm : IsAntisymm α le

  instance : Coe (PartialOrder α) (Preorder α) where
    coe PO := PO.toPreorder

  instance [P : PartialOrder α] : IsAntisymm α P.le :=
    P.toIsAntisymm

  theorem PartialOrder.le_antisymm'
    (P : PartialOrder α)
  : ∀ (a b : α), a ≤ b → b ≤ a → a = b :=
    P.toIsAntisymm.antisymm

  theorem PartialOrder.le_antisymm
    (P : PartialOrder α)
  : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
    fun {a b} => P.le_antisymm' a b

  instance [R : PartialOrder α] : _root_.PartialOrder α where
    toPreorder := inferInstance
    le_antisymm := R.le_antisymm'
end partial_order
