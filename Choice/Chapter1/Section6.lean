import Choice.Chapter1.Section5



namespace Choice



/-- An abstract choice function.-/
abbrev CFun (α : Type u) : Type u :=
  (S : Set α) → Set S



section
  variable
    {α : Type u}
    (cfun : CFun α)

  @[simp]
  abbrev _root_.Subtype.widen {S S' : Set α} (x : S) (sub : S ⊆ S') : S' :=
    { val := x.1, property := sub x.2 }
    

  abbrev CFun.P_α : Prop :=
    ∀ (S₁ S₂ : Set α) x,
      (h : x ∈ S₁) → (sub : S₁ ⊆ S₂)
      → {val := x, property := h : S₁.Elem}.widen sub ∈ cfun S₂
      → {val := x, property := h : S₁.Elem} ∈ cfun S₁

  abbrev CFun.P_β : Prop :=
    ∀ S₁ S₂, ∀ x ∈ cfun S₁, ∀ y ∈ cfun S₁,
      (sub : S₁ ⊆ S₂) → (x.widen sub ∈ cfun S₂ ↔ y.widen sub ∈ cfun S₂)
end



abbrev ProtoOrder.cfun
  (P : ProtoOrder α)
: CFun α :=
  fun S => (P.sub S).C



theorem lemma_1_m_α [P : ProtoOrder α] : P.cfun.P_α := by
  intro S₁ S₂ x x_in_S₁ S₁_sub_S₂
  simp [ProtoOrder.cfun, Set.mem_def, ProtoOrder.C, ProtoOrder.is_best]
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
    lt_def' := by simp [LT.lt]
    equiv_def' := by simp [HasEquiv.Equiv]
    toDecidableRel a b :=
      if h : a.le b then isTrue h else isFalse h
    toDecidableEq := inferInstance
  
  def Cex.toProtoOrder := instProtoOrderCex

  def Cex.Sxy : Set Cex
    | x | y => True
    | z => False
  def Cex.Sxyz : Set Cex
    | _ => True

  instance (cex : Cex) : Decidable (cex ∈ Cex.Sxy) := by
    simp [Set.mem_def, Cex.Sxy]
    cases cex <;> simp <;> try (apply isTrue True.intro)
    · apply isFalse
      intro
      assumption

  instance (cex : Cex) : Decidable (cex ∈ Cex.Sxyz) := by
    simp [Set.mem_def, Cex.Sxyz]
    cases cex <;> try (apply isTrue True.intro)

  theorem Cex.Sxy_sub_Sxyz : Sxy ⊆ Sxyz := by
    intro a
    simp [Set.mem_def, Sxy, Sxyz]

  def Cex.cfun : CFun Cex := fun S cex =>
    match cex.val with
    | x => True
    | y => z ∉ S
    | z => x ∉ S
  
  def Cex.cfun_eq : ∀ (S : Set Cex), cfun S = (Cex.toProtoOrder.sub S).M := by
    intro S
    ext a
    cases a with | mk val prop =>
    cases val <;> simp [Set.mem_def, cfun, Cex.toProtoOrder.lt_def]
    · intro a
      cases a <;> simp
    · constructor
      · intro not_z_in_S
        intro a
        cases a <;> simp
        · intro
          contradiction
      · intro h
        intro z_in_S
        let wrong := h z z_in_S
        let z_le_y : z ≤ y := by
          simp
        let wrong := wrong z_le_y
        simp at wrong
    · constructor
      · intro not_x_in_S
        intro a ; cases a <;> simp
        · intro
          contradiction
      · intro h
        intro x_in_S
        let wrong := h x x_in_S
        let x_le_z : x ≤ z := by
          simp
        let wrong := wrong x_le_z
        simp at wrong

  theorem Cex.x_in_Sxy : x ∈ Sxy := by
    simp [Set.mem_def]
  theorem Cex.y_in_Sxy : y ∈ Sxy := by
    simp [Set.mem_def]

  theorem Cex.x_in_Sxyz : x ∈ Sxyz := by
    simp [Set.mem_def]
  theorem Cex.y_in_Sxyz : y ∈ Sxyz := by
    simp [Set.mem_def]
  theorem Cex.z_in_Sxyz : z ∈ Sxyz := by
    simp [Set.mem_def]

  theorem Cex.x_in_cfun_Sxy : ⟨x, x_in_Sxy⟩ ∈ cfun Sxy := by
    simp [Set.mem_def, cfun]
  theorem Cex.y_in_cfun_Sxy : ⟨y, y_in_Sxy⟩ ∈ cfun Sxy := by
    simp [Set.mem_def, cfun]

  theorem Cex.x_in_cfun_Sxyz : ⟨x, x_in_Sxyz⟩ ∈ cfun Sxyz := by
    simp [Set.mem_def, cfun]
  theorem Cex.y_not_in_cfun_Sxyz : ⟨y, y_in_Sxyz⟩ ∉ cfun Sxyz := by
    simp [Set.mem_def, cfun]
end Lemma_1_m_β

open Lemma_1_m_β in
theorem lemma_1_m_β :¬ Cex.cfun.P_β := by
  simp only [CFun.P_β, not_forall]
  exists Cex.Sxy
  exists Cex.Sxyz
  exists ⟨Cex.x, Cex.x_in_cfun_Sxy⟩
  exists True.intro
  exists ⟨Cex.y, Cex.y_in_Sxy⟩
  exists Cex.y_in_cfun_Sxy
  exists Cex.Sxy_sub_Sxyz
  simp [Set.mem_def, Cex.cfun]



abbrev ProtoOrder.PiTransitive (_P : ProtoOrder α) : Prop :=
  ∀ {x y z : α}, x < y → y ≈ z → x < z

class ProtoOrder.IsPiTrans (P : ProtoOrder α) : Prop where
  pi_trans : P.PiTransitive



lemma lemma_1_n
  [P : ProtoOrder α]
  [T : IsTotal α P.le]
  [PiT : P.IsPiTrans]
: P.cfun.P_β := by
  intro S₁ S₂ x x_in_cfun_S₁ y y_in_cfun_S₁ S₁_sub_S₂
  cases x with | mk x x_in_S₁ =>
  cases y with | mk y y_in_S₁ =>
  simp [Set.mem_def, ProtoOrder.cfun]
  simp [Set.mem_def, ProtoOrder.cfun] at x_in_cfun_S₁ y_in_cfun_S₁
  constructor
  · intro C_x a
    let _x_le_a := C_x a
    cases a with | mk a a_in_S₂ =>
    simp [LE.le] at _x_le_a
    simp [LE.le]
    apply Decidable.byContradiction
    intro not_y_le_a

    let y_equiv_x : y ≈ x := by
      simp [P.equiv_def]
      constructor
      · apply y_in_cfun_S₁ ⟨x, x_in_S₁⟩
      · apply x_in_cfun_S₁ ⟨y, y_in_S₁⟩
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
  · intro C_y a
    let _y_le_a := C_y a
    cases a with | mk a a_in_S₂ =>
    simp [LE.le] at _y_le_a
    simp [LE.le]
    apply Decidable.byContradiction
    intro not_x_le_a

    let x_equiv_y : x ≈ y := by
      simp [P.equiv_def]
      constructor
      · apply x_in_cfun_S₁ ⟨y, y_in_S₁⟩
      · apply y_in_cfun_S₁ ⟨x, x_in_S₁⟩
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

