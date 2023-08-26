import Choice.Chapter1.Section4



namespace Choice



section def_1_8
  /-- True if every non-empty subset of `α` has a non-empty choice set. -/
  def ProtoOrder.ChoiceFun
    (P : ProtoOrder α)
  : Type u :=
    ∀ (S : Set α), [Inhabited S] → [∀ a, Decidable (a ∈ S)] → (P.sub S).C

  /-- Slightly more lax assumptions than `lemma_1_j`. -/
  abbrev ProtoOrder.ChoiceFunFin
    (P : ProtoOrder α)
  : Type u :=
    ∀ (S : Set α), [Finite S] → [Inhabited S] → [∀ a, Decidable (a ∈ S)] → (P.sub S).C


  namespace Order
    variable
      (O : Order α)

    abbrev ChoiceFun :=
      O.toPreorder.ChoiceFun
    abbrev ChoiceFunFin :=
      O.toPreorder.ChoiceFunFin

    def choiceFunFin : O.ChoiceFunFin := fun S =>
      O.sub S |>.getBest'
    
    def choiceFun
      [F : Finite α]
    : O.ChoiceFun := fun S =>
      let _ := F.sub S
      O.choiceFunFin S
  end Order


  namespace QOrder
    variable
      (Q : QOrder α)

    abbrev ChoiceFun :=
      Q.toQPreorder.ChoiceFun
    abbrev ChoiceFunFin :=
      Q.toQPreorder.ChoiceFunFin

    def choiceFunFin : Q.ChoiceFunFin := fun S =>
      Q.sub S |>.getBest'
    
    def choiceFun
      [F : Finite α]
    : Q.ChoiceFun := fun S =>
      let _ := F.sub S
      Q.choiceFunFin S
  end QOrder
end def_1_8



theorem lemma_1_j
  (O : Order α)
  [Finite α]
: O.ChoiceFunFin :=
  O.choiceFunFin


theorem lemma_1_k
  (Q : QOrder α)
  [Finite α]
: Q.ChoiceFunFin :=
  Q.choiceFunFin



/-! We're skipping `lemma_1_l` as it's messy to prove with the current architecture and it does not
seem to be used a whole lot after it's proved. -/



theorem Preorder.best_equiv
  [P : Preorder α]
  {b₁ : α}
: b₁ ∈ P.C → (∀ {b₂}, b₂ ∈ P.C ↔ b₁ ≈ b₂) := by
  intro C_b₁ b₂
  constructor
  · intro C_b₂
    rw [P.equiv_def]
    constructor
    · apply C_b₁ b₂
    · apply C_b₂ b₁
  · rw [P.equiv_def]
    intro b₁_equiv_b₂
    intro a
    let b₁_le_a := C_b₁ a
    apply P.le_trans b₁_equiv_b₂.right b₁_le_a
