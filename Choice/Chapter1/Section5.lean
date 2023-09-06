import Choice.Chapter1.Section4



/-! # Section 5

Introduces

- choice functions `ProtoOrder.ChoiceFun`;
-/
namespace Choice



/-! ## Definition `1*8` -/
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



  theorem ProtoOrder.le_total_of_choice_fun
    (P : ProtoOrder α)
    (cfun : P.ChoiceFun)
  : IsTotal α LE.le := by
    constructor
    intro a b
    let S : Set α := {a, b}
    let _ : Inhabited S :=
      ⟨⟨a, Set.mem_insert a {b}⟩⟩
    let _ : ∀ x, Decidable (x ∈ S) := by
      intro x
      simp [Set.mem_def]
      if ha : x = a then
        rw [ha]
        exact isTrue (Set.mem_insert a {b})
      else if hb : x = b then
        rw [hb]
        apply isTrue
        exact Set.mem_insert_of_mem a (Set.mem_singleton b)
      else
        apply isFalse
        intro x_in_S
        cases x_in_S with
        | inl x_eq_a =>
          contradiction
        | inr x_in_sub =>
          cases x_in_sub
          contradiction
    let ⟨⟨best, best_in_S⟩, C_best⟩ := cfun S
    simp [(P.sub S).C_def] at C_best
    cases best_in_S with
    | inl best_eq_a =>
      exact Or.inl (best_eq_a ▸ C_best.right)
    | inr best_in_sub =>
      cases best_in_sub
      exact Or.inr C_best.left

  theorem ProtoOrder.le_refl_of_choice_fun
    (P : ProtoOrder α)
    (cfun : P.ChoiceFun)
  : IsRefl α LE.le := by
    constructor
    intro a
    let S : Set α := {a}
    let _ : Inhabited S :=
      ⟨⟨a, Set.mem_singleton a⟩⟩
    let _ : ∀ x, Decidable (x ∈ S) := by
      intro x
      if h : x = a then
        rw [h]
        apply isTrue (Set.mem_singleton a)
      else
        apply isFalse
        intro x_in_S
        cases x_in_S
        contradiction
    let ⟨⟨best, best_in_S⟩, C_best⟩ := cfun S
    simp [(P.sub S).C_def] at C_best
    cases best_in_S
    assumption
  
  theorem ProtoOrder.sub_best_of_choice_fun
    (P : ProtoOrder α)
    (cfun : P.ChoiceFun)
    (S : Set α)
    [Inhabited S]
    [∀ a, Decidable (a ∈ S)]
  : ∀ (best : S), best ∈ (P.sub S).C → best ≈ (cfun S).1 := by
    intro best
    cases best with | mk best best_in_S =>
    simp [(P.sub S).C_def, (P.sub S).equiv_def, LE.le]
    cases cfun S with | mk wit C_wit =>
    simp [(P.sub S).C_def] at C_wit
    cases wit with | mk wit wit_in_S =>
    simp
    intro C_best
    constructor
    · exact C_best wit wit_in_S
    · exact C_wit best best_in_S



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



/-! ## Lemmas -/
section lemmas
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
end lemmas



/-! ## Lemma `1*l`

We're skipping `lemma_1_l` as it's messy to prove with the current architecture and it does not seem
to be used a whole lot after it's proved.
-/

