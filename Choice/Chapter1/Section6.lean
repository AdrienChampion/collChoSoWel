import Choice.Chapter1.Section5



/-! # Section 6

Introduces properties `α` and `β` for choice functions. We define these properties directly on
`ProtoOrder`s, seen as the result of applying the choice function.
-/
namespace Choice



instance decMem1
  {α : Type u} [D : DecidableEq α]
  {a : α}
: ∀ (x : α), Decidable (x ∈ ({a} : Set α)) := by
  intro x
  simp [Set.mem_singleton_iff]
  exact inferInstance

instance decMem2
  {α : Type u} [D : DecidableEq α]
  {a b : α}
: ∀ (x : α), Decidable (x ∈ ({a, b} : Set α)) := by
  intro x
  simp [Set.mem_insert_iff]
  exact inferInstance

instance decMem3
  {α : Type u} [D : DecidableEq α]
  {a b c : α}
: ∀ (x : α), Decidable (x ∈ ({a, b, c} : Set α)) := by
  intro x
  simp [Set.mem_insert_iff]
  exact inferInstance



section
  @[simp]
  abbrev _root_.Subtype.widen
    {S S' : Set α} (x : S) (sub : S ⊆ S')
  : S' :=
    { val := x.1, property := sub x.2 }

  variable
    {α : Type u}
    (P : ProtoOrder α)

  abbrev ProtoOrder.P_α : Prop :=
    ∀ (S₁ S₂ : Set α),
      [∀ a, Decidable (a ∈ S₁)]
      → [∀ a, Decidable (a ∈ S₂)]
      → ∀ x,
        (h : x ∈ S₁) → (sub : S₁ ⊆ S₂)
        → {val := x, property := h : S₁.Elem}.widen sub ∈ (P.sub S₂).C
        → {val := x, property := h : S₁.Elem} ∈ (P.sub S₁).C

  abbrev ProtoOrder.P_β : Prop :=
    ∀ (S₁ S₂ : Set α),
      [∀ a, Decidable (a ∈ S₁)]
      → [∀ a, Decidable (a ∈ S₂)]
      → ∀ x ∈ (P.sub S₁).C, ∀ y ∈ (P.sub S₁).C,
        (sub : S₁ ⊆ S₂) → (x.widen sub ∈ (P.sub S₂).C ↔ y.widen sub ∈ (P.sub S₂).C)
end



theorem lemma_1_m_α [P : ProtoOrder α] : P.P_α := by
  intro S₁ S₂ _ _ x x_in_S₁ S₁_sub_S₂
  simp [Set.mem_def, ProtoOrder.C, ProtoOrder.is_best]
  intro best_S₂ a a_in_S₁
  apply best_S₂
  apply S₁_sub_S₂ a_in_S₁



/-! Counterexample for `CFun.P_β` for a choice function derived from a `ProtoOrder`. -/
namespace Lemma_1_m_β
  inductive Cex | x | y | z
  deriving Repr, Inhabited

  def Cex.beq : Cex → Cex → Bool
  | x, x | y, y | z, z => true
  | _, _ => false

  instance : BEq Cex := ⟨Cex.beq⟩

  instance : LawfulBEq Cex where
    eq_of_beq {a b} h := by
      simp [BEq.beq, Cex.beq] at h
      split at h <;> try rfl
      contradiction
    rfl {a} := by
      simp [BEq.beq, Cex.beq]
      cases a <;> rfl

  instance : DecidableEq Cex := by
    intro a b
    cases a
    <;> cases b
    <;> (
      try (apply isTrue rfl)
      try (apply isFalse ; simp)
    )

  @[simp]
  def Cex.le : Cex → Cex → Bool
  | x, x | y, y | z, z
  | x, _ | y, x | z, y => true
  | z, x | y, z => false

  theorem Cex.le_refl' a : Cex.le a a := by
    cases a <;> simp

  instance : LE Cex where
    le a b := Cex.le a b
  instance : LT Cex where
    lt a b := a ≤ b ∧ ¬ b ≤ a
  instance : HasEquiv Cex where
    Equiv a b := a ≤ b ∧ b ≤ a
  
  instance instProtoOrderCex : ProtoOrder Cex where
    toDecidableRel a b :=
      if h : a.le b then isTrue h else isFalse h
    toDecidableEq := inferInstance
  
  def Cex.toProtoOrder := instProtoOrderCex

  def Cex.Sxy : Set Cex :=
    {x, y}
  def Cex.Sxyz : Set Cex :=
    {x, y, z}

  instance decMemSxy : ∀ (cex : Cex), Decidable (cex ∈ Cex.Sxy) :=
    decMem2

  instance decMemSxyz : ∀ (cex : Cex), Decidable (cex ∈ Cex.Sxyz) :=
    decMem3

  theorem Cex.Sxy_sub_Sxyz : Sxy ⊆ Sxyz := by
    intro a
    simp [Sxy, Sxyz]
    intro h
    cases h <;> simp [*]

  def Cex.cfun : Cex.toProtoOrder.ChoiceFun := fun S I _ => by
    if x_in_S : x ∈ S then
      constructor
      case val => exact ⟨x, x_in_S⟩
      · simp [ProtoOrder.C_def, LE.le]
        intro a _
        cases a <;> simp [LE.le]
    else if z_in_S : z ∈ S then
      constructor
      case val => exact ⟨z, z_in_S⟩
      · simp [ProtoOrder.C_def, LE.le]
        intro a _
        cases a <;> simp [LE.le]
        contradiction
    else if y_in_S : y ∈ S then
      constructor
      case val => exact ⟨y, y_in_S⟩
      · simp [ProtoOrder.C_def, LE.le]
        intro a _
        cases a <;> simp [LE.le]
        contradiction
    else
      cases I.default with | mk a a_in_S =>
      cases a <;> contradiction

  theorem Cex.x_in_Sxy : x ∈ Sxy := by
    simp [Set.mem_def]
  theorem Cex.y_in_Sxy : y ∈ Sxy := by
    simp [Set.mem_def]
  theorem Cex.z_not_in_Sxy : z ∉ Sxy := by
    simp [Set.mem_def]

  theorem Cex.x_in_Sxyz : x ∈ Sxyz := by
    simp [Set.mem_def]
  theorem Cex.y_in_Sxyz : y ∈ Sxyz := by
    simp [Set.mem_def]
  theorem Cex.z_in_Sxyz : z ∈ Sxyz := by
    simp [Set.mem_def]

  theorem Cex.x_in_C_Sxy : ⟨x, x_in_Sxy⟩ ∈ (Cex.toProtoOrder.sub Sxy).C := by
    simp [ProtoOrder.C_def]
    intro a _
    cases a <;> simp [LE.le]
  theorem Cex.y_in_C_Sxy : ⟨y, y_in_Sxy⟩ ∈ (Cex.toProtoOrder.sub Sxy).C := by
    simp [ProtoOrder.C_def]
    intro a _
    cases a <;> simp [LE.le]
    apply z_not_in_Sxy
    assumption

  theorem Cex.x_in_C_Sxyz : ⟨x, x_in_Sxyz⟩ ∈ (Cex.toProtoOrder.sub Sxyz).C := by
    simp [ProtoOrder.C_def]
    intro a _
    cases a <;> simp [LE.le]
  theorem Cex.y_not_in_C_Sxyz : ⟨y, y_in_Sxyz⟩ ∉ (Cex.toProtoOrder.sub Sxyz).C := by
    simp [ProtoOrder.C_def]
    exists z
  theorem Cex.z_not_in_C_Sxyz : ⟨z, z_in_Sxyz⟩ ∉ (Cex.toProtoOrder.sub Sxyz).C := by
    simp [ProtoOrder.C_def]
    exists x
end Lemma_1_m_β

open Lemma_1_m_β in
theorem lemma_1_m_β : ¬ Cex.toProtoOrder.P_β := by
  simp only [ProtoOrder.P_β, not_forall]
  exists Cex.Sxy
  exists Cex.Sxyz
  exists inferInstance
  exists inferInstance
  exists ⟨Cex.x, Cex.x_in_Sxy⟩
  exists Cex.x_in_C_Sxy
  exists ⟨Cex.y, Cex.y_in_Sxy⟩
  exists Cex.y_in_C_Sxy
  exists Cex.Sxy_sub_Sxyz
  simp [ProtoOrder.C_def, LE.le]
  intro h
  let h' : ∀ a, a ∈ Cex.Sxyz → Cex.x ≤ a := by
    intro a a_in_Sxyz
    cases a <;> simp [LE.le]
  let h := h.mp h' Cex.z Cex.z_in_Sxyz
  simp [LE.le] at h



abbrev ProtoOrder.PiTransitive (_P : ProtoOrder α) : Prop :=
  ∀ {x y z : α}, x < y → y ≈ z → x < z

class ProtoOrder.IsPiTrans (P : ProtoOrder α) : Prop where
  pi_trans : P.PiTransitive



abbrev ProtoOrder.IpTransitive (_P : ProtoOrder α) : Prop :=
  ∀ {x y z : α}, x ≈ y → y < z → x < z

class ProtoOrder.IsIpTrans (P : ProtoOrder α) : Prop where
  ip_trans : P.IpTransitive



abbrev ProtoOrder.IiTransitive (_P : ProtoOrder α) : Prop :=
  ∀ {x y z : α}, x ≈ y → y ≈ z → x ≈ z

class ProtoOrder.IsIiTrans (P : ProtoOrder α) : Prop where
  ii_trans : P.IiTransitive



theorem lemma_1_n
  [P : ProtoOrder α]
  (cfun : P.ChoiceFun)
: P.P_β ↔ P.IsPiTrans := by
  let T := P.le_total_of_choice_fun cfun
  let R := P.le_refl_of_choice_fun cfun
  constructor
  · intro Pβ
    constructor
    intro a b c
    rw [P.lt_def, P.equiv_def, and_imp, and_imp]
    intro _ab nba bc cb
    apply Decidable.byContradiction
    intro h
    let ca := P.not_lt h
    let S₁ : Set α := {b, c}
    let S₂ : Set α := {a, b, c}
    let S₁_sub_S₂ : S₁ ⊆ S₂ := Set.subset_insert a S₁
    let _ : ∀ a, Decidable (a ∈ S₁) := decMem2
    let _ : ∀ a, Decidable (a ∈ S₂) := decMem3
    let b_in_S₁ : b ∈ S₁ := by simp
    -- let b_in_S₂ : b ∈ S₂ := by simp
    let c_in_S₁ : c ∈ S₁ := by simp
    -- let c_in_S₂ : c ∈ S₂ := by simp
    let b_in_C_S₁ : ⟨b, b_in_S₁⟩ ∈ (P.sub S₁).C := by
      simp [ProtoOrder.C_def]
      exact ⟨(refl b), bc⟩
    let c_in_C_S₁ : ⟨c, c_in_S₁⟩ ∈ (P.sub S₁).C := by
      simp [ProtoOrder.C_def]
      exact ⟨cb, (refl c)⟩
    -- let c_in_C_S₂ : ⟨c, c_in_S₂⟩ ∈ (P.sub S₂).C := by
    --   simp [ProtoOrder.C_def]
    --   exact ⟨ca, cb, (refl c)⟩
    let h :=
      Pβ {b, c} {a, b, c}
        ⟨c, c_in_S₁⟩ c_in_C_S₁
        ⟨b, b_in_S₁⟩ b_in_C_S₁
        S₁_sub_S₂
      |>.mp
    simp [ProtoOrder.C_def] at h
    let tmp := h ca cb (refl c)
    exact nba tmp.left
  · intro PiT S₁ S₂ _ _ x x_in_C_S₁ y y_in_C_S₁ S₁_sub_S₂
    cases x with | mk x x_in_S₁ =>
    cases y with | mk y y_in_S₁ =>
    simp [ProtoOrder.C_def]
    simp [ProtoOrder.C_def] at x_in_C_S₁ y_in_C_S₁
    constructor
    · intro C_x a a_in_S₂
      let _x_le_a := C_x a a_in_S₂
      apply Decidable.byContradiction
      intro not_y_le_a

      let y_equiv_x : y ≈ x := by
        simp [P.equiv_def]
        constructor
        · apply y_in_C_S₁ x x_in_S₁
        · apply x_in_C_S₁ y y_in_S₁
      let a_lt_y : a < y := by
        simp [P.lt_def]
        constructor
        · let res := T.total a y
          simp [not_y_le_a] at res
          exact res
        · exact not_y_le_a
      let not_x_le_a : ¬ x ≤ a := by
        let res := PiT.pi_trans a_lt_y y_equiv_x
        simp [P.lt_def] at res
        exact res.right
      contradiction
    · intro C_y a a_in_S₂
      let _y_le_a := C_y a a_in_S₂
      simp [LE.le] at _y_le_a
      simp [LE.le]
      apply Decidable.byContradiction
      intro not_x_le_a

      let x_equiv_y : x ≈ y := by
        simp [P.equiv_def]
        constructor
        · apply x_in_C_S₁ y y_in_S₁
        · apply y_in_C_S₁ x x_in_S₁
      let a_lt_x : a < x := by
        simp [P.lt_def]
        constructor
        · let res := T.total a x
          simp [not_x_le_a] at res
          exact res
        · exact not_x_le_a
      let not_y_le_a : ¬ y ≤ a := by
        let res := PiT.pi_trans a_lt_x x_equiv_y
        simp [P.lt_def] at res
        exact res.right
      
      contradiction



/-- Skipping the `a)` of `lemma_1_o` part that quasi-trans and PI-trans are independent. -/
theorem lemma_1_o_b
  [P : ProtoOrder α]
  [PP : IsPpTrans α]
  [PI : P.IsPiTrans]
  (cfun : P.ChoiceFun)
: Transitive P.le := by
  let T := P.le_total_of_choice_fun cfun
  intro a b c a_le_b b_le_c
  apply Decidable.byContradiction
  intro not_a_le_c
  let c_lt_a : c < a := by
    let c_le_a : c ≤ a := by
      let res := T.total a c
      simp [not_a_le_c] at res
      exact res
    simp [P.lt_def]
    exact ⟨c_le_a, not_a_le_c⟩
  if b_le_a : b ≤ a then
    let a_equiv_b : a ≈ b := by
      simp [P.equiv_def]
      constructor <;> assumption
    let not_b_le_c := by
      let res := PI.pi_trans c_lt_a a_equiv_b
      simp [P.lt_def] at res
      exact res.right
    contradiction
  else
    let a_lt_b : a < b := by
      simp [P.lt_def]
      exact ⟨a_le_b, b_le_a⟩
    let not_b_le_c := by
      let res := Trans.trans c_lt_a a_lt_b
      simp [P.lt_def] at res
      exact res.right
    contradiction



theorem lemma_1_p
  [P : ProtoOrder α]
  [Pi : P.IsPiTrans]
  (cfun : P.ChoiceFun)
: Transitive P.le :=
  let T := P.le_total_of_choice_fun cfun
  let _R := P.le_refl_of_choice_fun cfun
  let Pp : IsPpTrans α := by
    constructor
    intro a b c
    simp [P.lt_def]
    intro _ab nba bc ncb
    let nca : ¬ c ≤ a := by
      intro ca
      if ac : a ≤ c then
        let b_lt_a := Pi.pi_trans ⟨bc, ncb⟩ ⟨ca, ac⟩
        exact nba b_lt_a.left
      else
        let S : Set α := {a, b, c}
        let _ : Inhabited S :=
          ⟨by
            let a_in_S : a ∈ S := by
              simp
            exact ⟨a, a_in_S⟩⟩
        let ⟨⟨cex, cex_in_S⟩, C_cex⟩ := cfun S
        simp [ProtoOrder.C_def] at C_cex
        cases Set.eq_or_mem_of_mem_insert cex_in_S with
        | inl cex_eq_a =>
          let _ := cex_eq_a ▸ C_cex.right.right
          contradiction
        | inr cex_in_tl =>
          cases cex_in_tl with
          | inl cex_eq_b =>
            let _ := cex_eq_b ▸ C_cex.left
            contradiction
          | inr cex_in_tl =>
            cases cex_in_tl with
            | refl =>
              let _ := C_cex.right.left
              contradiction

    apply And.intro _ nca
    let res := T.total a c
    simp [nca] at res
    exact res
  lemma_1_o_b cfun



theorem lemma_1_q
  [P : ProtoOrder α]
  (cfun : P.ChoiceFun)
: P.P_β ↔ ∃ (O : Order α), O.toProtoOrder = P := by
  let T := P.le_total_of_choice_fun cfun
  let R := P.le_refl_of_choice_fun cfun

  constructor
  · intro Pβ
    let PiT := lemma_1_n cfun |>.mp Pβ
    let Tr := lemma_1_p cfun
    let O : Order α := {
      toProtoOrder := P,
      le_refl' := R.refl
      le_trans' := Tr
      le_total' := T.total
    }
    exists O
  · intro ex
    cases ex with | intro O h_O =>
    rw [← h_O] at *
    cases O with | mk le_total =>
    rename Preorder α => P'
    cases P' with | mk le_refl le_trans =>
    intro S₁ S₂ _ _ x C_x₁ y C_y₁ sub
    cases x with | mk x x_in_S₁ =>
    cases y with | mk y y_in_S₁ =>
    simp [ProtoOrder.C_def, LE.le]
    simp [ProtoOrder.C_def, LE.le] at C_x₁ C_y₁
    constructor
    · intro C_x₂
      intro a a_in_S₂
      rw [h_O] at *
      apply le_trans (C_y₁ x x_in_S₁) (C_x₂ a a_in_S₂)
    · intro C_y₂
      intro a a_in_S₂
      rw [h_O] at *
      apply le_trans (C_x₁ y y_in_S₁) (C_y₂ a a_in_S₂)



theorem lemma_1_r_a
  [P : ProtoOrder α]
  [T : IsTotal α LE.le]
: P.IsPiTrans ↔ P.IsIpTrans := by
  constructor
  · intro PiT
    constructor
    intro a b c a_equiv_b b_lt_c
    apply Decidable.byContradiction
    intro not_a_lt_c
    let ca := P.not_lt not_a_lt_c
    if ac : a ≤ c then
      let b_lt_a := PiT.pi_trans b_lt_c ⟨ca, ac⟩
      apply b_lt_a.right a_equiv_b.left
    else
      let c_lt_b := PiT.pi_trans ⟨ca, ac⟩ a_equiv_b
      apply b_lt_c.right c_lt_b.left
  · intro IpT
    constructor
    intro a b c a_lt_b b_equiv_c
    apply Decidable.byContradiction
    intro not_a_lt_c
    let ca := P.not_lt not_a_lt_c
    if ac : a ≤ c then
      let c_lt_b := IpT.ip_trans ⟨ca, ac⟩ a_lt_b
      apply c_lt_b.right b_equiv_c.left
    else
      let c_lt_b := IpT.ip_trans b_equiv_c ⟨ca, ac⟩
      apply c_lt_b.right a_lt_b.left

theorem lemma_1_r_b
  [P : ProtoOrder α]
  [T : IsTotal α LE.le]
: P.IsPiTrans → P.IsIiTrans := by
  intro PiT
  constructor
  intro a b c a_equiv_b b_equiv_c
  apply Decidable.byContradiction
  simp only [P.equiv_def, not_and_or]
  intro h
  cases h with
  | inl nac =>
    let ca := T.total a c
    simp [nac] at ca
    let c_lt_b := PiT.pi_trans ⟨ca, nac⟩ a_equiv_b
    apply c_lt_b.right
    exact b_equiv_c.left
  | inr nca =>
    let ac := T.total a c
    simp [nca] at ac
    let a_lt_b := PiT.pi_trans ⟨ac, nca⟩ (symm b_equiv_c)
    apply a_lt_b.right
    exact a_equiv_b.right

theorem lemma_1_r_c
  [P : ProtoOrder α]
  [T : IsTotal α LE.le]
  [PpT : IsPpTrans α]
  [IiT : P.IsIiTrans]
: P.IsPiTrans := by
  constructor
  intro a b c
  intro a_lt_b b_equiv_c
  apply Decidable.byContradiction
  intro h
  let ca := P.not_lt h
  if ac : a ≤ c then
    let a_equiv_b := IiT.ii_trans ⟨ac, ca⟩ (symm b_equiv_c)
    apply a_lt_b.right a_equiv_b.right
  else
    let c_lt_b := PpT.pp_trans ⟨ca, ac⟩ a_lt_b
    apply c_lt_b.right b_equiv_c.left
