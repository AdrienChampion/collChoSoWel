import Choice.Chapter3.Reframe
import Choice.Chapter3.Swf



namespace Choice



/-! ## Pair-specific `*Order` generation

Given `a b : α` with `a ≠ b`, we want to generate `*Order`-s where the only non-reflexive `≤`
relation is `a ≤ b`. Hence, we have `a < b`.
-/
section genLt
  variable
    {α : Type u}
    [Finite α]
    [DecidableEq α]
    {a b : α}

  def ProtoOrder.genLt (_a_ne_b : a ≠ b) : ProtoOrder α where
    le x y :=
      (x = a ∧ y = b) ∨ x = y
    toDecidableRel := by
      simp [DecidableRel]
      exact inferInstance
    toDecidableEq :=
      inferInstance

  def ProtoOrder.genLt_post {a_ne_b : a ≠ b} : ProtoOrder.genLt a_ne_b |>.lt a b := by
    simp [ProtoOrder.genLt]
    intro h
    cases h with
    | inl h =>
      rw [h.left] at a_ne_b
      contradiction
    | inr h =>
      rw [h] at a_ne_b
      contradiction

  def Preorder.genLt (a_ne_b : a ≠ b) : Preorder α where
    toProtoOrder := ProtoOrder.genLt a_ne_b
    le_refl' x := by
      simp [ProtoOrder.toLE, LE.le, ProtoOrder.genLt]
    le_trans' x y z := by
      simp [ProtoOrder.toLE, LE.le, ProtoOrder.genLt]
      intro h h'
      cases h <;> cases h'
      case inl.inl h h' =>
        exact Or.inl ⟨h.left, h'.right⟩
      case inr.inr h h' =>
        simp [h, h']
      case inl.inr h h' =>
        rw [← h', h.left, h.right]
        exact Or.inl ⟨rfl, rfl⟩
      case inr.inl h h' =>
        rw [h, h'.left, h'.right]
        exact Or.inl ⟨rfl, rfl⟩

  def Preorder.genLt_post (a_ne_b : a ≠ b) : Preorder.genLt a_ne_b |>.lt a b :=
    ProtoOrder.genLt_post

  def Order.genLt (a_ne_b : a ≠ b) : Order α :=
    let P := Preorder.genLt a_ne_b
    P.totalize

  theorem Order.genLt_post (a_ne_b : a ≠ b) : (Order.genLt a_ne_b).lt a b := by
    let ⟨a_le_b, h⟩ :=
      (Preorder.genLt a_ne_b).totalize_subrel a b (Preorder.genLt_post a_ne_b).left
    constructor ; exact a_le_b
    exact h (Preorder.genLt_post a_ne_b).right
end genLt



theorem lemma_3_xz'
  (swf : Swf α count)
  (chs : Choices.Ordered α count)
  (J : chs.Idx)
  (x y z : α)
  (J_x_lt_y : chs[J].lt x y)
  (J_y_lt_z : chs[J].lt y z)
  (O_y_lt_x : ∀ (i : Set.compl {J}), chs[i.1].lt y x)
  (O_y_lt_z : ∀ (i : Set.compl {J}), chs[i.1].lt y z)
: swf.almost_decisive {J} x y
  → swf.Wpp
  → (swf chs).lt x z
:= by
  simp only [Swf.almost_decisive]
  intro aldec wpp
  let x_lt_y :=
    let h : ∀ (i : ({J} : Set chs.Idx)), chs[i.1].lt x y := by
      intro i
      cases i with | mk i i_eq_J =>
      simp at i_eq_J
      simp [i_eq_J]
      exact J_x_lt_y
    aldec chs h O_y_lt_x
  let y_lt_z :=
    let h : ∀ (i : chs.Idx), chs[i].lt y z := by
      intro i
      if h_i_eq_J : i = J then
        simp [h_i_eq_J]
        exact J_y_lt_z
      else
        let i_in_compl_J : i ∈ Set.compl {J} := by
          apply Set.mem_compl
          intro wrong
          cases wrong
          contradiction
        apply O_y_lt_z
          ⟨i, i_in_compl_J⟩
    wpp chs y z h
  let x_lt_z :=
    (swf chs).lt_trans x_lt_y y_lt_z
  exact x_lt_z

theorem lemma_3_zy'
  (swf : Swf α count)
  (chs : Choices.Ordered α count)
  (J : chs.Idx)
  (x y z : α)
  (J_z_lt_x : chs[J].lt z x)
  (J_x_lt_y : chs[J].lt x y)
  (O_z_lt_x : ∀ (i : Set.compl {J}), chs[i.1].lt z x)
  (O_y_lt_x : ∀ (i : Set.compl {J}), chs[i.1].lt y x)
: swf.almost_decisive {J} x y
  → swf.Wpp
  → (swf chs).lt z y
:= by
  simp only [Swf.almost_decisive]
  intro aldec wpp
  let z_lt_x :=
    let h : ∀ (i : chs.Idx), chs[i].lt z x := by
      intro i
      if h_i_eq_J : i = J then
        simp [h_i_eq_J]
        exact J_z_lt_x
      else
        let i_in_compl_J : i ∈ Set.compl {J} := by
          apply Set.mem_compl
          intro wrong
          cases wrong
          contradiction
        apply O_z_lt_x
          ⟨i, i_in_compl_J⟩
    wpp chs z x h
  let x_lt_y :=
    let h : ∀ (i : ({J} : Set chs.Idx)), chs[i.1].lt x y := by
      intro i
      cases i with | mk i i_eq_J =>
      simp at i_eq_J
      simp [i_eq_J]
      exact J_x_lt_y
    aldec chs h O_y_lt_x
  let z_lt_y :=
    (swf chs).lt_trans z_lt_x x_lt_y
  exact z_lt_y


theorem lemma_3_xz
  [Finite α]
  (swf : Swf α count)
  (chs : Choices.Ordered α count)
  (J : chs.Idx)
  (x y z : α)
  (x_ne_y : x ≠ y)
  (y_ne_z : y ≠ z)
  (J_x_lt_z : chs[J].lt x z)
: swf.almost_decisive {J} x y
  → swf.Wpp
  → swf.Iia
  → (swf chs).lt x z
:= by
  intro aldec wpp iia

  let x_ne_z : x ≠ z := by
    intro h
    rw [h] at J_x_lt_z
    let _ := chs[J]
    exact instIsIrreflLT.irrefl z J_x_lt_z

  -- tagged as dead code while used everywhere...
  let _f' (i : chs.Idx) :=
    if h_i : J = i
    then chs[i].reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z (h_i ▸ J_x_lt_z)
    else chs[i].reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z
  cases J with | mk J h_J =>
  let f i (_O : Order α) := _f' i

  let chs' := chs.map f

  let get_chs'_def (i : chs.Idx) : chs'[i.1] = _f' i :=
    chs.getElem_map f i

  let J_chs'_def
  : chs'[J] = chs[J].reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z J_x_lt_z := by
    let tmp := get_chs'_def ⟨J, h_J⟩
    rw [tmp]
    simp
  let other_chs'_def
    (i : chs.Idx)
    (h_i_ne_J : i.1 ≠ J)
  : chs'[i.1] = chs[i].reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z := by
    rw [get_chs'_def i]
    simp
    intro i_def
    rw [Fin.mk_eq_mk] at i_def
    let _ := h_i_ne_J i_def.symm
    contradiction

  let J'_x_lt_y : chs'[J].lt x y := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_xy x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
  let J'_y_lt_z : chs'[J].lt y z := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_yz x y z x_ne_y x_ne_z y_ne_z J_x_lt_z

  let O'_y_lt_x : ∀ (i : Set.compl {Fin.mk J h_J}), chs'[i.1].lt y x := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_yx_yz_post_yx x y z x_ne_y x_ne_z y_ne_z
  let O'_y_lt_z : ∀ (i : Set.compl {Fin.mk J h_J}), chs'[i.1].lt y z := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_yx_yz_post_yz x y z x_ne_y x_ne_z y_ne_z

  let chs'_x_lt_z :=
    lemma_3_xz'
      swf chs' ⟨J, h_J⟩
      x y z
      J'_x_lt_y J'_y_lt_z
      O'_y_lt_x O'_y_lt_z
      aldec
      wpp

  apply swf.iia_lt (x := x) (y := z) iia chs' chs
  · intro i
    if h_i : J = i then
      simp [Choices.getElem_map, h_i]
      constructor
      · exact
        chs[i].reframe_xy_yz_post_xz x y z x_ne_y x_ne_z y_ne_z
          (by cases h_i ; exact J_x_lt_z)
        |>.symm
      · exact
        chs[i].reframe_xy_yz_post_zx x y z x_ne_y x_ne_z y_ne_z
          (by cases h_i ; exact J_x_lt_z)
        |>.symm
    else
      let h_i : ¬ ⟨J, h_J⟩ = i :=
        by rw [Fin.mk_eq_mk] ; exact h_i
      simp [Choices.getElem_map, h_i]
      constructor
      · exact
        chs[i].reframe_yx_yz_post_xz x y z x_ne_y x_ne_z y_ne_z
        |>.symm
      · exact
        chs[i].reframe_yx_yz_post_zx x y z x_ne_y x_ne_z y_ne_z
        |>.symm
  · exact chs'_x_lt_z


theorem lemma_3_zy
  [Finite α]
  (swf : Swf α count)
  (chs : Choices.Ordered α count)
  (J : chs.Idx)
  (x y z : α)
  (x_ne_y : x ≠ y)
  (x_ne_z : x ≠ z)
  (J_z_lt_y : chs[J].lt z y)
: swf.almost_decisive {J} x y
  → swf.Wpp
  → swf.Iia
  → (swf chs).lt z y
:= by
  intro aldec wpp iia

  let y_ne_z : y ≠ z := by
    intro h
    rw [h] at J_z_lt_y
    let _ := chs[J]
    exact instIsIrreflLT.irrefl z J_z_lt_y

  -- tagged as dead code while used everywhere...
  let _f' (i : chs.Idx) :=
    if h_i : J = i
    then chs[i].reframe_xy_yz z x y x_ne_z.symm y_ne_z.symm x_ne_y (h_i ▸ J_z_lt_y)
    else chs[i].reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z
  cases J with | mk J h_J =>
  let f i (_O : Order α) := _f' i

  let chs' := chs.map f

  let get_chs'_def (i : chs.Idx) : chs'[i.1] = _f' i :=
    chs.getElem_map f i

  let J_chs'_def
  : chs'[J] = chs[J].reframe_xy_yz z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y := by
    let tmp := get_chs'_def ⟨J, h_J⟩
    rw [tmp]
    simp
  let other_chs'_def
    (i : chs.Idx)
    (h_i_ne_J : i.1 ≠ J)
  : chs'[i.1] = chs[i].reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z := by
    rw [get_chs'_def i]
    simp
    intro i_def
    rw [Fin.mk_eq_mk] at i_def
    let _ := h_i_ne_J i_def.symm
    contradiction

  let J'_z_lt_x : chs'[J].lt z x := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_xy z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
  let J'_x_lt_y : chs'[J].lt x y := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_yz z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y

  let O'_z_lt_x : ∀ (i : Set.compl {Fin.mk J h_J}), chs'[i.1].lt z x := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_zx_yx_post_zx x y z x_ne_y x_ne_z y_ne_z
  let O'_y_lt_x : ∀ (i : Set.compl {Fin.mk J h_J}), chs'[i.1].lt y x := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_zx_yx_post_yx x y z x_ne_y x_ne_z y_ne_z

  let chs'_z_lt_y :=
    lemma_3_zy'
      swf chs' ⟨J, h_J⟩
      x y z
      J'_z_lt_x J'_x_lt_y
      O'_z_lt_x O'_y_lt_x
      aldec
      wpp

  apply swf.iia_lt (x := z) (y := y) iia chs' chs
  · intro i
    if h_i : J = i then
      simp [Choices.getElem_map, h_i]
      constructor
      · exact
        chs[i].reframe_xy_yz_post_xz z x y x_ne_z.symm y_ne_z.symm x_ne_y
          (by cases h_i ; exact J_z_lt_y)
        |>.symm
      · exact
        chs[i].reframe_xy_yz_post_zx z x y x_ne_z.symm y_ne_z.symm x_ne_y
          (by cases h_i ; exact J_z_lt_y)
        |>.symm
    else
      let h_i : ¬ ⟨J, h_J⟩ = i :=
        by rw [Fin.mk_eq_mk] ; exact h_i
      simp [Choices.getElem_map, h_i]
      constructor
      · exact
        chs[i].reframe_zx_yx_post_zy x y z x_ne_y x_ne_z y_ne_z
        |>.symm
      · exact
        chs[i].reframe_zx_yx_post_yz x y z x_ne_y x_ne_z y_ne_z
        |>.symm
  · exact chs'_z_lt_y


theorem lemma_3_a_1
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (x_ne_y : x ≠ y)
  (y_ne_z : y ≠ z)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: swf.almost_decisive {J} x y
  → swf.decisive {J} x z
:= by
  intro aldec chs J_x_lt_z
  simp at J_x_lt_z
  let x_lt_z := lemma_3_xz swf chs J x y z x_ne_y y_ne_z J_x_lt_z aldec wpp iia
  simp [Swf.decisive]
  exact x_lt_z


theorem lemma_3_a_2
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (x_ne_y : x ≠ y)
  (x_ne_z : x ≠ z)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: swf.almost_decisive {J} x y
  → swf.decisive {J} z y
:= by
  intro aldec chs J_z_lt_y
  simp at J_z_lt_y
  let z_lt_y := lemma_3_zy swf chs J x y z x_ne_y x_ne_z J_z_lt_y aldec wpp iia
  simp [Swf.decisive]
  intros
  exact z_lt_y


theorem lemma_3_a_3
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (x_ne_z : x ≠ z)
  (x_ne_y : x ≠ y)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: swf.almost_decisive {J} x z
  → swf.decisive {J} y z
:=
  lemma_3_a_2 swf x_ne_z x_ne_y wpp iia


theorem lemma_3_a_4
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (y_ne_z : y ≠ z)
  (z_ne_x : z ≠ x)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: swf.almost_decisive {J} y z
  → swf.decisive {J} y x
:=
  lemma_3_a_1 swf y_ne_z z_ne_x wpp iia



theorem lemma_3_a_5
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (x_ne_y : x ≠ y)
  (x_ne_z : x ≠ z)
  (y_ne_z : y ≠ z)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: swf.almost_decisive {J} x y → swf.decisive {J} y x := fun aldec =>
  lemma_3_a_1 swf x_ne_y y_ne_z wpp iia aldec
  |> swf.almost_decisive_of_decisive
  |> lemma_3_a_3 swf x_ne_z x_ne_y wpp iia
  |> swf.almost_decisive_of_decisive
  |> lemma_3_a_4 swf y_ne_z x_ne_z.symm wpp iia


theorem lemma_3_a_6
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (x_ne_y : x ≠ y)
  (x_ne_z : x ≠ z)
  (y_ne_z : y ≠ z)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: swf.almost_decisive {J} y x
  → swf.decisive {J} y z
  ∧ swf.decisive {J} z x
  ∧ swf.decisive {J} x y
:= fun aldec =>
  let dec_yz := lemma_3_a_1 swf x_ne_y.symm x_ne_z wpp iia aldec
  let dec_zx := lemma_3_a_2 swf x_ne_y.symm y_ne_z wpp iia aldec
  let dec_xy := lemma_3_a_5 swf x_ne_y.symm y_ne_z x_ne_z wpp iia aldec
  ⟨dec_yz, dec_zx, dec_xy⟩


theorem lemma_3_a_7
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (x_ne_y : x ≠ y)
  (x_ne_z : x ≠ z)
  (y_ne_z : y ≠ z)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: swf.almost_decisive {J} x y
  → swf.decisive {J} y z
  ∧ swf.decisive {J} z x
  ∧ swf.decisive {J} x y
:= fun aldec =>
  let dec_yx := lemma_3_a_5 swf x_ne_y x_ne_z y_ne_z wpp iia aldec
  let aldec_yx := swf.almost_decisive_of_decisive dec_yx
  lemma_3_a_6 swf x_ne_y x_ne_z y_ne_z wpp iia aldec_yx


theorem lemma_1_a_partialDictator
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (x_ne_y : x ≠ y)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: ∀ (z : α),
  x ≠ z
  → y ≠ z
  → swf.almost_decisive {J} x y
  → swf.partialDictator J {x, y, z}
:= fun z x_ne_z y_ne_z aldec_xy ⟨a, a_in_S⟩ ⟨b, b_in_S⟩ chs => by
  let dec_xz :=
    lemma_3_a_1 swf x_ne_y y_ne_z wpp iia aldec_xy
  let dec_yx :=
    lemma_3_a_5 swf x_ne_y x_ne_z y_ne_z wpp iia aldec_xy
  let dec_zy :=
    lemma_3_a_2 swf x_ne_y x_ne_z wpp iia aldec_xy
  let ⟨dec_yz, dec_zx, dec_xy⟩ :=
    lemma_3_a_7 swf x_ne_y x_ne_z y_ne_z wpp iia aldec_xy
  simp [ProtoOrder.lt_def]
  simp at a_in_S b_in_S
  cases a_in_S <;> cases b_in_S
  case inl.inl h_ax h_bx =>
    rw [h_ax, h_bx]
    simp [Preorder.le_refl]
  case inl.inr h_ax h_b =>
    cases h_b with
    | inl h_by =>
      rw [h_ax, h_by]
      intro xy nyx
      exact dec_xy chs (by simp ; exact ⟨xy, nyx⟩)
    | inr h_bz =>
      rw [h_ax, h_bz]
      intro xz nzx
      exact dec_xz chs (by simp ; exact ⟨xz, nzx⟩)
  case inr.inl h_a h_bx =>
    cases h_a with
    | inl h_ay =>
      rw [h_ay, h_bx]
      intro yx nxy
      exact dec_yx chs (by simp ; exact ⟨yx, nxy⟩)
    | inr h_az =>
      rw [h_az, h_bx]
      intro zx nxz
      exact dec_zx chs (by simp ; exact ⟨zx, nxz⟩)
  case inr.inr h_a h_b =>
    cases h_a <;> cases h_b
    case inl.inl h_ay h_by =>
      rw [h_ay, h_by]
      simp [Preorder.le_refl]
    case inl.inr h_ay h_bz =>
      rw [h_ay, h_bz]
      intro yz nzy
      exact dec_yz chs (by simp ; exact ⟨yz, nzy⟩)
    case inr.inl h_az h_by =>
      rw [h_az, h_by]
      intro zy nyz
      exact dec_zy chs (by simp ; exact ⟨zy, nyz⟩)
    case inr.inr h_az h_bz =>
      rw [h_az, h_bz]
      simp [Preorder.le_refl]


theorem lemma_1_a
  [Finite α]
  (swf : Swf α count)
  {J : Fin count}
  (wpp : swf.Wpp)
  (iia : swf.Iia)
  (x y z : α)
  (x_ne_y : x ≠ y)
  (x_ne_z : x ≠ z)
  (y_ne_z : y ≠ z)
: swf.almost_decisive {J} x y
  → swf.dictator J
:= fun aldec_xy u v => by
  let dec_yx :=
    lemma_3_a_5 swf x_ne_y x_ne_z y_ne_z wpp iia aldec_xy
  let ⟨_, _, dec_xy⟩ :=
    lemma_3_a_7 swf x_ne_y x_ne_z y_ne_z wpp iia aldec_xy
  if h_uv : u = v then
    rw [h_uv]
    exact swf.decisive_refl
  else if h_ux : u = x then
    if h_vx : v = x then
      rw [h_ux, h_vx] at h_uv
      contradiction
    else if h_vy : v = y then
      rw [h_ux, h_vy]
      exact dec_xy
    else
      rw [h_ux]
      exact lemma_3_a_1 swf x_ne_y h_vy.ne_symm wpp iia aldec_xy
  else if h_uy : u = y then
    if h_vx : v = x then
      rw [h_uy, h_vx]
      exact dec_yx
    else if h_vy : v = y then
      rw [h_uy, h_vy] at h_uv
      contradiction
    else
      rw [h_uy]
      apply
        lemma_3_a_7 swf
          (x := x) (y := y) (z := v)
          x_ne_y h_vx.ne_symm h_vy.ne_symm
          wpp iia aldec_xy
        |>.left
  else
    if h_vx : v = x then
      rw [h_vx]
      exact
        lemma_3_a_7 swf
          x_ne_y h_ux.ne_symm h_uy.ne_symm
          wpp iia aldec_xy
        |>.right
        |>.left
    else if h_vy : v = y then
      rw [h_vy]
      exact
        lemma_3_a_2 swf x_ne_y h_ux.ne_symm wpp iia aldec_xy
    else
      let aldec_xu : swf.almost_decisive {J} x u :=
        lemma_3_a_1 swf
          x_ne_y (fun h => by let _ := h.symm ; contradiction)
          wpp iia aldec_xy
        |> swf.almost_decisive_of_decisive
      exact
        lemma_3_a_7 swf h_ux.ne_symm h_vx.ne_symm h_uv wpp iia aldec_xu
        |>.left



/-! ## Proof switch

From this point forward we rely on the proof from

- <https://www.rochester.edu/college/faculty/markfey/papers/ArrowProof3.pdf>

More precisely, we prove *Step 1* and *Step 2* which gives us a `J` that's decisive for some pair of
elements. We can then conclude with `lemma_1_a` above.
 -/


theorem lemma_3_1_find_J'
  [Finite α]
  (swf : Swf α count)
  (h_count : 1 < count)
  (wpp : swf.Wpp)
  (a b : α)
  (map : Fin (count + 1) → (Choices.Ordered α count))
  (h_map :
    ∀ (j : Fin (count + 1)) (i : Fin count),
      if i.1 < j.1
      then (map j)[i].lt b a
      else (map j)[i].lt a b)
: ∃ (J : Fin count),
  (swf (map ⟨J.1, Nat.lt_succ_of_lt J.2⟩)).lt a b
  ∧ (swf (map ⟨J.1 + 1, Nat.succ_lt_succ J.2⟩)).le b a
:=
  let chs0_a_lt_b : (swf (map 0)).lt a b :=
    wpp _ a b (h_map 0)
  aux ⟨0, Nat.lt_of_succ_lt h_count⟩ chs0_a_lt_b
where
  aux
    (j : Fin count) (h : swf (map ⟨j.1, Nat.lt_succ_of_lt j.2⟩) |>.lt a b)
  := by
    let simp_count : count - 1 + 1 = count := by
      apply Nat.succ_pred
      simp
      intro wrong
      rw [wrong] at h_count
      contradiction
    cases j with | mk j h_j =>
    if h_j' : j + 1 < count then
      let j' := j + 1
      let h_j'' : j + 1 < count + 1 :=
        Nat.lt_succ_of_lt h_j'
      if h' : swf (map ⟨j', h_j''⟩) |>.lt a b then
        exact aux ⟨j', h_j'⟩ h'
      else
        let b_le_a : swf (map ⟨j', h_j''⟩) |>.le b a := by
          simp at h'
          cases swf (map ⟨j', h_j''⟩) |>.le_total' b a with
          | inl _ => assumption
          | inr h => exact h' h
        exists ⟨j, h_j⟩
    else
      let j_def : j = count - 1 := by
        simp at h_j'
        cases Nat.lt_or_eq_of_le h_j' with
        | inl wrong =>
          exfalso
          cases Nat.lt_or_eq_of_le wrong with
          | inl succ_lt_succ =>
            let count_lt_j := Nat.lt_of_succ_lt_succ succ_lt_succ
            exact Nat.lt_asymm h_j count_lt_j
          | inr succ_eq_succ =>
            simp at succ_eq_succ
            simp [succ_eq_succ] at h_j
        | inr h_eq =>
          simp [h_eq]
      cases j_def
      clear j_def

      let count_legit : count < count + 1 := by
        rw [Nat.lt_succ]
      let b_lt_a : swf (map ⟨count, count_legit⟩) |>.lt b a :=
        wpp _ _ _ (fun i => by
          let _h := h_map ⟨count, count_legit⟩ i
          cases i with | mk i h_i =>
          simp [simp_count] at _h
          simp [Fin.lt_def, h_i, Nat.le_pred_of_lt h_i] at _h
          exact ⟨_h.left, _h.right⟩)
      let n_a_lt_b : ¬ (swf (map ⟨count, count_legit⟩) |>.lt a b) := fun a_lt_b =>
        b_lt_a.right a_lt_b.left
      exists ⟨count - 1, h_j⟩
      constructor
      · exact h
      · simp [simp_count]
        simp at n_a_lt_b
        cases swf (map ⟨count, count_legit⟩) |>.le_total' b a with
        | inl _ => assumption
        | inr h =>
          exact n_a_lt_b h
  termination_by aux i _ => count - i



theorem lemma_3_1_find_J
  [Finite α]
  [DecidableEq α]
  (swf : Swf α count)
  (h_count : 1 < count)
  (wpp : swf.Wpp)
  {a b : α}
  (a_ne_b : a ≠ b)
: ∃ (J : Fin count) (chs chs' : Choices.Ordered α count),
    (∀ (i : Fin count),
      if i.1 < J.1
      then chs[i].lt b a
      else chs[i].lt a b)
    ∧
    (∀ (i : Fin count),
      if i.1 ≤ J.1
      then chs'[i].lt b a
      else chs'[i].lt a b)
    ∧ (swf chs).lt a b
    ∧ (swf chs').le b a
:= by
  let map (j : Fin (count + 1)) : Choices.Ordered α count :=
    Choices.mk fun i =>
      if i.1 < j.1
      then Order.genLt a_ne_b.symm
      else Order.genLt a_ne_b
  let map_post
    (j : Fin (count + 1)) (i : Fin count)
  : if i.1 < j.1 then (map j)[i] |>.lt b a else (map j)[i] |>.lt a b := by
    simp
    simp [Order.toPreorder, Preorder.toProtoOrder, LE.le]
    split
    case inl h_i =>
      simp [ProtoOrder.toLE, Choices.get, getElem, h_i]
      exact Order.genLt_post a_ne_b.symm
    case inr h_i =>
      simp [ProtoOrder.toLE, Choices.get, getElem, h_i]
      exact Order.genLt_post a_ne_b
  let ⟨J, post_a_lt_b, post_b_le_a⟩ :=
    lemma_3_1_find_J' swf h_count wpp a b map map_post

  exists J, map ⟨J.1, Nat.lt_succ_of_lt J.2⟩, map ⟨J.1 + 1, Nat.succ_lt_succ J.2⟩
  constructor
  · intro i
    split
    case inl h_i =>
      let h_i' : i < J := by
        rw [Fin.lt_def]
        exact h_i
      simp [Choices.get, getElem, h_i']
      exact Order.genLt_post a_ne_b.symm
    case inr h_i =>
      let h_i' : ¬ i < J := by
        rw [Fin.lt_def]
        exact h_i
      simp [Choices.get, getElem, h_i']
      exact Order.genLt_post a_ne_b
  constructor
  · intro i
    split
    case inl h_i =>
      let h_i' : i.1 < J.1 + 1 :=
        Nat.lt_succ_of_le h_i
      simp [Choices.get, getElem, h_i']
      exact Order.genLt_post a_ne_b.symm
    case inr h_i =>
      let h_i' : ¬ i.1 < J.1 + 1 := by
        intro h
        apply h_i
        exact Nat.le_of_lt_succ h
      simp [Choices.get, getElem, h_i']
      exact Order.genLt_post a_ne_b
  constructor
  · exact post_a_lt_b
  · exact post_b_le_a





theorem lemma_3_1_2'
  [Finite α]
  (swf : Swf α count)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
  (a b c : α)
  (J : Fin count)
  (chs chs' : Choices.Ordered α count)
  (chs_ab : ∀ (i : Fin count),
    if i.1 < J.1
    then chs[i].lt b a
    else chs[i].lt a b)
  (chs_a_lt_b : swf chs |>.lt a b)
  (chs'_ab : ∀ (i : Fin count),
    if i.1 < J.1
    then chs'[i].lt b a
    else chs'[i].lt a b)
  (chs'_bc : ∀ (i : Fin count), chs'[i].lt b c)
: (swf chs').lt a c := by
  let S : Set α := {a, b}
  let S_C_eq_C' :=
    iia chs chs' S (by
      simp [Preorder.le_refl]
      constructor <;> (
        intro i
        simp [Order.toPreorder, Preorder.toProtoOrder, ProtoOrder.toLE]
        let chs_i := chs_ab i
        let chs'_i := chs'_ab i
        if h : i.1 < J.1 then
          simp only [h] at chs_i chs'_i
          simp at chs_i chs'_i
          simp [chs_i, chs'_i]
        else
          simp only [h] at chs_i chs'_i
          dsimp at chs_i chs'_i
          simp [chs'_i, chs_i]
      )
    )
  let chs'_a_lt_b :=
    Preorder.sub_pair_lt_subst S_C_eq_C' chs_a_lt_b
  apply (swf chs').lt_trans chs'_a_lt_b
  apply wpp
  intro i
  exact chs'_bc i

theorem lemma_3_1_2
  [Finite α]
  (swf : Swf α count)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
  (a b c: α)
  (a_ne_b : a ≠ b)
  (a_ne_c : a ≠ c)
  (b_ne_c : b ≠ c)
  (J : Fin count)
  (chs : Choices.Ordered α count)
  (chs_ab : ∀ (i : Fin count),
    if i.1 < J.1
    then chs[i].lt b a
    else chs[i].lt a b)
  (chs_a_lt_b : swf chs |>.lt a b)
: ∃ (chs' : Choices.Ordered α count),
    (∀ (i : Fin count),
      if i.1 < J.1
      then chs'[i].lt c a
      else chs'[i].lt a c)
    ∧ (swf chs').lt a c
:= by
  let h_b_lt_a (i : Fin count) (h_i : i.1 < J.1) : chs[i].lt b a := by
    let res := chs_ab i
    simp only [h_i] at res
    simp at res
    exact res

  let f' (i : Fin count) : Order α :=
    if h_i : i.1 < J.1 then
      chs[i].reframe_xy_yz b c a b_ne_c a_ne_b.symm a_ne_c.symm (h_b_lt_a i h_i)
    else
      chs[i].reframe_zx_yx c a b a_ne_c.symm b_ne_c.symm a_ne_b
  let f i (_ : Order α) := f' i

  let chs' := chs.map f

  let chs'_ab :
    ∀ (i : Fin count),
      if i.1 < J.1
      then chs'[i].lt b a
      else chs'[i].lt a b
  := by
    intro i
    if h_i : i < J then
      simp [h_i, Choices.getElem_map]
      let ab :=
        chs[i].reframe_xy_yz_post_xz b c a b_ne_c a_ne_b.symm a_ne_c.symm (h_b_lt_a i h_i)
      let ba :=
        chs[i].reframe_xy_yz_post_zx b c a b_ne_c a_ne_b.symm a_ne_c.symm (h_b_lt_a i h_i)
      rw [← ab, ← ba]
      let res := chs_ab i
      simp [h_i] at res
      exact res
    else
      simp [h_i, Choices.getElem_map]
      let ab :=
        chs[i].reframe_zx_yx_post_yz c a b a_ne_c.symm b_ne_c.symm a_ne_b
      let ba :=
        chs[i].reframe_zx_yx_post_zy c a b a_ne_c.symm b_ne_c.symm a_ne_b
      rw [← ab, ← ba]
      let res := chs_ab i
      simp [h_i] at res
      exact res

  let chs'_bc : ∀ (i : Fin count), chs'[i].lt b c := by
    intro i
    if h_i : i < J then
      simp [Choices.getElem_map, h_i]
      exact chs[i].reframe_xy_yz_post_xy b c a b_ne_c a_ne_b.symm a_ne_c.symm (h_b_lt_a i h_i)
    else
      simp [Choices.getElem_map, h_i]
      exact chs[i].reframe_zx_yx_post_zx c a b a_ne_c.symm b_ne_c.symm a_ne_b

  let chs_map_a_lt_c :=
    lemma_3_1_2' swf wpp iia a b c J chs chs' chs_ab chs_a_lt_b chs'_ab chs'_bc

  let chs'_ac :
    ∀ (i : Fin count),
      if i.1 < J.1
      then chs'[i].lt c a
      else chs'[i].lt a c
  := by
    intro i
    if h_i : i < J then
      simp [Choices.getElem_map, h_i]
      exact chs[i].reframe_xy_yz_post_yz b c a b_ne_c a_ne_b.symm a_ne_c.symm (h_b_lt_a i h_i)
    else
      simp [Choices.getElem_map, h_i]
      exact chs[i].reframe_zx_yx_post_yx c a b a_ne_c.symm b_ne_c.symm a_ne_b

  exists chs.map f



theorem lemma_3_1_3'
  [Finite α]
  (swf : Swf α count)
  (iia : swf.Iia)
  (a b c: α)
  (J : Fin count)
  (chs chs' chs'' : Choices.Ordered α count)
  (chs_ab : ∀ (i : Fin count),
    if i.1 ≤ J.1
    then chs[i].lt b a
    else chs[i].lt a b)
  (chs_b_le_a : swf chs |>.le b a)
  (chs'_ac : ∀ (i : Fin count),
    if i.1 < J.1
    then chs'[i].lt c a
    else chs'[i].lt a c)
  (chs'_a_lt_c : swf chs' |>.lt a c)
  (chs''_ab : ∀ (i : Fin count),
    if i.1 ≤ J.1
    then chs''[i].lt b a
    else chs''[i].lt a b)
  (chs''_ac : ∀ (i : Fin count),
    if i.1 < J.1
    then chs''[i].lt c a
    else chs''[i].lt a c)
: (swf chs'').lt b c := by
  let chs''_a_lt_c : (swf chs'').lt a c :=
    let S : Set α := {a, c}
    let S_C'_eq_C'' :=
      iia chs' chs'' S (by
        simp [Preorder.le_refl]
        constructor <;> (
          intro i
          simp [Order.toPreorder, Preorder.toProtoOrder, ProtoOrder.toLE]
          let chs'_i := chs'_ac i
          let chs''_i := chs''_ac i
          if h : i.1 < J.1 then
            simp only [h] at chs'_i chs''_i
            simp at chs'_i chs''_i
            simp [chs'_i, chs''_i]
          else
            simp only [h] at chs'_i chs''_i
            dsimp at chs'_i chs''_i
            simp [chs'_i, chs''_i]
        )
      )
    Preorder.sub_pair_lt_subst S_C'_eq_C'' chs'_a_lt_c

  let chs''_b_le_a : (swf chs'').le b a :=
    let S : Set α := {b, a}
    let S_C_eq_C'' :=
      iia chs chs'' S (by
        simp [Preorder.le_refl]
        constructor <;> (
          intro i
          simp [Order.toPreorder, Preorder.toProtoOrder, ProtoOrder.toLE]
          let chs_i := chs_ab i
          let chs''_i := chs''_ab i
          if h : i.1 ≤ J.1 then
            simp only [h] at chs_i chs''_i
            simp at chs_i chs''_i
            simp [chs_i, chs''_i]
          else
            simp only [h] at chs_i chs''_i
            dsimp at chs_i chs''_i
            simp [chs_i, chs''_i]
        )
      )
    Preorder.sub_pair_le_subst S_C_eq_C'' chs_b_le_a
  constructor
  · exact (swf chs'').le_trans chs''_b_le_a chs''_a_lt_c.left
  · intro chs''_c_le_b
    apply chs''_a_lt_c.right
    exact (swf chs'').le_trans chs''_c_le_b chs''_b_le_a



theorem lemma_3_1_3
  [Finite α]
  [DecidableEq α]
  (swf : Swf α count)
  (h_count : 1 < count)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
  (a b c : α)
  (a_ne_b : a ≠ b) (a_ne_c : a ≠ c) (b_ne_c : b ≠ c)
: ∃ (J : Fin count), swf.decisive {J} b c := by

  let ⟨J, tmp_chs, chs'', tmp_chs_ab, chs''_ab, tmp_chs_a_lt_b, chs''_b_le_a⟩ :=
    lemma_3_1_find_J swf h_count wpp a_ne_b

  let ⟨chs', chs'_ac, chs'_a_lt_c⟩ :=
    lemma_3_1_2 swf wpp iia a b c a_ne_b a_ne_c b_ne_c J tmp_chs tmp_chs_ab tmp_chs_a_lt_b
  clear tmp_chs tmp_chs_ab tmp_chs_a_lt_b

  exists J
  intro chs chs_J_b_lt_c
  simp at chs_J_b_lt_c

  let f' (i : Fin count) : Order α :=
    if i.1 < J.1 then
      chs[i].reframe_zx_yx a b c a_ne_b a_ne_c b_ne_c
    else if i.1 = J.1 then
      chs[J].reframe_xy_yz b a c a_ne_b.symm b_ne_c a_ne_c chs_J_b_lt_c
    else
      chs[i].reframe_yx_yz b a c a_ne_b.symm b_ne_c a_ne_c
  let f i (_ : Order α) := f' i

  let chs_map := chs.map f

  let chs_map_iff_bc_cb :
    ∀ (i : Fin count),
      (chs_map[i].le b c ↔ chs[i].le b c)
      ∧ (chs_map[i].le c b ↔ chs[i].le c b)
  := by
    intro i
    rw [chs.getElem_map f i]
    if h_i : i < J then
      simp [h_i]
      constructor
      · exact chs[i].reframe_zx_yx_post_yz a b c a_ne_b a_ne_c b_ne_c
        |>.symm
      · exact chs[i].reframe_zx_yx_post_zy a b c a_ne_b a_ne_c b_ne_c
        |>.symm
    else if h_i' : i = J then
      simp [h_i, h_i']
      constructor
      · exact chs[J].reframe_xy_yz_post_xz b a c a_ne_b.symm b_ne_c a_ne_c chs_J_b_lt_c
        |>.symm
      · exact chs[J].reframe_xy_yz_post_zx b a c a_ne_b.symm b_ne_c a_ne_c chs_J_b_lt_c
        |>.symm
    else
      rw [Fin.mk_eq_mk] at h_i'
      simp [h_i, h_i']
      constructor
      · exact chs[i].reframe_yx_yz_post_xz b a c a_ne_b.symm b_ne_c a_ne_c
        |>.symm
      · exact chs[i].reframe_yx_yz_post_zx b a c a_ne_b.symm b_ne_c a_ne_c
        |>.symm

  let chs_map_ab :
    ∀ (i : Fin count),
      if i.1 ≤ J.1
      then chs_map[i].lt b a
      else chs_map[i].lt a b
  := by
    intro i
    split
    case inl i_le_J =>
      cases Nat.le_iff_lt_or_eq.mp i_le_J with
      | inl i_lt_J =>
        let h_i : i < J := Fin.mk_lt_mk.mpr i_lt_J
        simp [Choices.getElem_map, h_i]
        exact chs[i].reframe_zx_yx_post_yx a b c a_ne_b a_ne_c b_ne_c
      | inr i_eq_J =>
        let h_i : i = J := Fin.mk_eq_mk.mpr i_eq_J
        simp [Choices.getElem_map, h_i]
        exact chs[J].reframe_xy_yz_post_xy b a c a_ne_b.symm b_ne_c a_ne_c chs_J_b_lt_c
    case inr h_i =>
      let h_i' : ¬ i < J := by
        intro h
        apply h_i
        rw [Fin.mk_lt_mk] at h
        exact Nat.le_of_lt h
      let h_i'' : ¬ i.1 = J.1 := by
        intro h
        apply h_i
        rw [h]
      simp [Choices.getElem_map, h_i', h_i'']
      exact chs[i].reframe_yx_yz_post_yx b a c a_ne_b.symm b_ne_c a_ne_c

  let chs_map_ac :
    ∀ (i : Fin count),
      if i.1 < J.1
      then chs_map[i].lt c a
      else chs_map[i].lt a c
  := by
    intro i
    split
    case inl i_lt_J =>
      let h_i : i < J := Fin.mk_lt_mk.mpr i_lt_J
      simp [Choices.getElem_map, h_i]
      exact chs[i].reframe_zx_yx_post_zx a b c a_ne_b a_ne_c b_ne_c
    case inr h_i =>
      simp [Choices.getElem_map, h_i]
      if h_i' : i = J then
        simp [h_i']
        exact chs[J].reframe_xy_yz_post_yz b a c a_ne_b.symm b_ne_c a_ne_c chs_J_b_lt_c
      else
        let h_i : ¬ i < J := by
          rw [Fin.mk_lt_mk]
          assumption
        let h_i' : ¬ i.1 = J.1 := by
          rw [← Fin.mk_eq_mk]
          assumption
        simp [h_i, h_i']
        exact chs[i].reframe_yx_yz_post_yz b a c a_ne_b.symm b_ne_c a_ne_c

  let b_lt_c :=
    lemma_3_1_3'
      swf iia a b c J
      chs'' chs' chs_map
      chs''_ab chs''_b_le_a
      chs'_ac chs'_a_lt_c
      chs_map_ab
      chs_map_ac

  apply swf.iia_lt iia chs_map chs chs_map_iff_bc_cb b_lt_c


theorem lemma_3_1
  [Finite α]
  [DecidableEq α]
  (swf : Swf α count)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
  (h_count : 1 < count)
  (a b c : α)
  (a_ne_b : a ≠ b)
  (a_ne_c : a ≠ c)
  (b_ne_c : b ≠ c)
: ∃ (J : Fin count), swf.dictator J :=
  let ⟨J, J_dec⟩ :=
    lemma_3_1_3 swf h_count wpp iia a b c a_ne_b a_ne_c b_ne_c
  let J_aldec :=
    swf.almost_decisive_of_decisive J_dec
  let J_dictator :=
    lemma_1_a swf wpp iia b c a
      b_ne_c a_ne_b.symm a_ne_c.symm J_aldec
  ⟨J, J_dictator⟩
