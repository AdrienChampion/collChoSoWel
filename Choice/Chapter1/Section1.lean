import Choice.Init



/-! # Section 1.1 -/
namespace Choice



class ProtoOrder (α : Type u) extends LE α, LT α, HasEquiv α where
  decidableRel : DecidableRel le
  decidableEq : DecidableEq α
  lt_def (a b : α) : a < b ↔ a ≤ b ∧ ¬ b ≤ a
  equiv_def (a b : α) : a ≈ b ↔ a ≤ b ∧ b ≤ a

instance [I : ProtoOrder α] : DecidableRel I.le :=
  I.decidableRel
instance [I : ProtoOrder α] : DecidableRel I.lt := by
  intro a b
  simp [I.lt_def]
  apply inferInstance
instance [I : ProtoOrder α] : DecidableEq α :=
  I.decidableEq

/-- `R`elation of weak preference, noted `a ≤ b`. -/
abbrev R [ProtoOrder α] (a b : α) :=
  a ≤ b
def ProtoOrder.R := @Choice.R

/-- `P`reference, noted `a < b`. -/
abbrev P [ProtoOrder α] (a b : α) :=
  a < b
def ProtoOrder.P := @Choice.P

instance [R : ProtoOrder α] : IsIrrefl α R.lt where
  irrefl a := by
    simp [R.lt_def]

instance [R : ProtoOrder α] [IsTrans α R.le] : IsTrans α R.lt where
  trans a b c := by
    simp [R.lt_def]
    intro aRb _not_bRa bRc not_cRb
    apply And.intro (_root_.trans aRb bRc)
    intro cRa
    apply not_cRb
    exact _root_.trans cRa aRb

abbrev ProtoOrder.equiv [R : ProtoOrder α] :=
  R.Equiv

/-- `I`ndifference, noted `a ≈ b`. -/
abbrev I [ProtoOrder α] (a b : α) :=
  a ≈ b
def ProtoOrder.I := @Choice.I

instance [R : ProtoOrder α] [IsRefl α R.le] : IsRefl α R.Equiv where
  refl a := by
    simp [R.equiv_def, refl]

instance [R : ProtoOrder α] [IsTrans α R.le] : IsTrans α R.Equiv where
  trans a b c := by
    simp [R.equiv_def]
    intro aRb bRa bRc cRb
    exact And.intro (_root_.trans aRb bRc) (_root_.trans cRb bRa)



section
  class Preorder (α : Type u) extends ProtoOrder α where
    le_refl : Reflexive le
    le_trans : Transitive le

  instance instRootPreorderOfPreorder [R : Preorder α] : _root_.Preorder α where
    toLE := R.toLE
    toLT := R.toLT
    le_refl := R.le_refl
    le_trans := R.le_trans
    lt_iff_le_not_le := R.lt_def

  class Order (α : Type u) extends Preorder α where
    le_total : Total le

  class PartialOrder (α : Type u) extends Preorder α where
    le_antisymm : Antisymm le

  instance [R : PartialOrder α] : _root_.PartialOrder α where
    toPreorder := instRootPreorderOfPreorder
    le_antisymm := by
      let h := R.le_antisymm
      unfold Antisymm at h
      apply fun _ _ => R.le_antisymm.antisymm
end
