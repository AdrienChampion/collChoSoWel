import Choice.Init



/-! # Section 1.1 -/
namespace Choice



class ProtoOrder (α : Type u) extends LE α, LT α, HasEquiv α where
  toDecidableRel : DecidableRel toLE.le
  toDecidableEq : DecidableEq α
  lt_def' (a b : α) : a < b ↔ a ≤ b ∧ ¬ b ≤ a
  equiv_def' (a b : α) : a ≈ b ↔ a ≤ b ∧ b ≤ a

section
  variable (P : ProtoOrder α)

  abbrev ProtoOrder.lt_def {a b} :=
    P.lt_def' a b

  abbrev ProtoOrder.equiv_def {a b} :=
    P.equiv_def' a b

  abbrev ProtoOrder.equiv :=
    P.Equiv
end



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
  variable [P : ProtoOrder α]



  instance : DecidableRel P.le :=
    P.toDecidableRel

  instance : DecidableRel P.lt := by
    intro a b
    simp [P.lt_def]
    apply inferInstance

  instance : DecidableEq α :=
    P.toDecidableEq



  instance : IsIrrefl α P.lt where
    irrefl a := by
      simp [P.lt_def]

  instance [IsTrans α P.le] : IsTrans α P.lt where
    trans a b c := by
      simp [P.lt_def]
      intro aRb _not_bRa bRc not_cRb
      apply And.intro (_root_.trans aRb bRc)
      intro cRa
      apply not_cRb
      exact _root_.trans cRa aRb

  instance [IsRefl α P.le] : IsRefl α P.Equiv where
    refl a := by
      simp [P.equiv_def, refl]

  instance [IsTrans α P.le] : IsTrans α P.Equiv where
    trans a b c := by
      simp [P.equiv_def]
      intro aRb bRa bRc cRb
      exact And.intro (_root_.trans aRb bRc) (_root_.trans cRb bRa)
end



section
  class QPreorder (α : Type u) extends ProtoOrder α where
    le_refl' : Reflexive le
    /-- `Transitive lt` corresponds to the book's notion of quasi-transitivity. -/
    lt_trans' : Transitive lt

  instance : Coe (QPreorder α) (ProtoOrder α) where
    coe Q := Q.toProtoOrder
  instance [Q : QPreorder α] : IsTrans α Q.lt :=
    ⟨Q.lt_trans'⟩


  
  section
    variable (Q : QPreorder α)

    def QPreorder.le_refl {a} :=
      Q.le_refl' a
    def QPreorder.lt_trans {a b c : α} : a < b → b < c → a < c :=
      Q.lt_trans' (x := a) (y := b) (z := c)
  end



  class Preorder (α : Type u) extends ProtoOrder α where
    le_refl' : Reflexive le
    le_trans' : Transitive le
  
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
      lt_trans' := P.lt_trans'
    
    instance : Coe (Preorder α) (QPreorder α) where
      coe P := P.toQPreorder

    instance [P : Preorder α] : QPreorder α :=
      P.toQPreorder
  end



  instance instRootPreorderOfPreorder [R : Preorder α] : _root_.Preorder α where
    toLE := R.toLE
    toLT := R.toLT
    le_refl := R.le_refl'
    le_trans := R.le_trans'
    lt_iff_le_not_le _ _ := R.lt_def



  class QOrder (α : Type u) extends QPreorder α where
    le_total : Total le

  instance : Coe (QOrder α) (QPreorder α) where
    coe Q := Q.toQPreorder



  class Order (α : Type u) extends Preorder α where
    le_total : Total le

  def Order.toQOrder (O : Order α) : QOrder α where
    toQPreorder := O.toPreorder.toQPreorder
    le_total := O.le_total

  instance : Coe (Order α) (Preorder α) where
    coe O := O.toPreorder



  class PartialOrder (α : Type u) extends Preorder α where
    le_antisymm : Antisymm le

  instance : Coe (PartialOrder α) (Preorder α) where
    coe PO := PO.toPreorder

  instance [R : PartialOrder α] : _root_.PartialOrder α where
    toPreorder := instRootPreorderOfPreorder
    le_antisymm := by
      let h := R.le_antisymm
      unfold Antisymm at h
      apply fun _ _ => R.le_antisymm.antisymm
end
