import Choice.Chapter2
import Choice.Chapter3.Reframe
import Choice.Chapter3.Swf



namespace Choice



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
  let _f (i : chs.Idx) :=
    if h_i : J = i
    then chs[i].reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z (h_i ▸ J_x_lt_z)
    else chs[i].reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z
  cases J with | mk J h_J =>
  let f' i (_O : Order α) := _f i

  let get_chs'_def (i : chs.Idx) : (chs.map f')[i.1] = _f i :=
    chs.getElem_map f' i

  let J_chs'_def
  : (chs.map f')[J] = chs[J].reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z J_x_lt_z := by
    let tmp := get_chs'_def ⟨J, h_J⟩
    rw [tmp]
    simp
  let other_chs'_def
    (i : chs.Idx)
    (h_i_ne_J : i.1 ≠ J)
  : (chs.map f')[i.1] = chs[i].reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z := by
    rw [get_chs'_def i]
    simp
    intro i_def
    rw [Fin.mk_eq_mk] at i_def
    let _ := h_i_ne_J i_def.symm
    contradiction

  let J'_x_lt_y : (chs.map f')[J].lt x y := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_xy x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
  let J'_y_lt_z : (chs.map f')[J].lt y z := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_yz x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
  -- let J'_x_lt_z : (chs.map f')[J].lt x z := by
  --   rw [J_chs'_def]
  --   constructor
  --   · exact chs[J].reframe_xy_yz_post_xz x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
  --     |>.mp J_x_lt_z.left
  --   · exact chs[J].reframe_xy_yz_post_zx x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
  --     |>.not.mp J_x_lt_z.right

  let O'_y_lt_x : ∀ (i : Set.compl {Fin.mk J h_J}), (chs.map f')[i.1].lt y x := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_yx_yz_post_yx x y z x_ne_y x_ne_z y_ne_z
  let O'_y_lt_z : ∀ (i : Set.compl {Fin.mk J h_J}), (chs.map f')[i.1].lt y z := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_yx_yz_post_yz x y z x_ne_y x_ne_z y_ne_z

  let S : Set α := {x, z}
  let x_in_S : x ∈ S := Set.mem_insert x {z}
  let z_in_S : z ∈ S := Set.mem_insert_iff.mpr (Or.inr $ Set.mem_singleton z)
  let chs'_x_lt_z :=
    lemma_3_xz'
      swf (chs.map f') ⟨J, h_J⟩
      x y z
      J'_x_lt_y J'_y_lt_z
      O'_y_lt_x O'_y_lt_z
      aldec
      wpp

  let C_eq_C' :=
    iia
      chs (chs.map f') {x, z}
      (fun ⟨a, a_in_S⟩ ⟨b, b_in_S⟩ ⟨i, h_i⟩ => by
        simp at a_in_S b_in_S
        simp
        cases a_in_S <;> cases b_in_S
        case inl.inl h h' =>
          rw [h, h']
          simp [Preorder.le_refl]
        case inr.inr h h' =>
          rw [h, h']
          simp [Preorder.le_refl]
        case inl.inr h h' =>
          rw [h, h']
          if h_iJ : i = J then
            cases h_iJ
            constructor
            · intro chs_x_le_z
              apply Order.le_subst _ _ J_chs'_def.symm
              apply chs[J].reframe_xy_yz_post_xz x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
                |>.mp chs_x_le_z
            · intro chs'_x_le_z
              apply chs[J].reframe_xy_yz_post_xz x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
                |>.mpr
              exact (chs.map f')[J].le_subst _ J_chs'_def chs'_x_le_z
          else
            constructor
            · intro chs_x_le_z
              apply
                (chs[i].reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ).symm
              apply chs[i].reframe_yx_yz_post_xz x y z x_ne_y x_ne_z y_ne_z |>.mp chs_x_le_z
            · intro chs'_x_le_z
              rw [chs[i].reframe_yx_yz_post_xz x y z x_ne_y x_ne_z y_ne_z]
              apply
                (chs.map f')[i].le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ)
              apply chs'_x_le_z
        case inr.inl h h' =>
          rw [h, h']
          if h_iJ : i = J then
            cases h_iJ
            constructor
            · intro chs_z_le_x
              apply Order.le_subst _ _ J_chs'_def.symm
              apply chs[J].reframe_xy_yz_post_zx x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
                |>.mp chs_z_le_x
            · intro chs'_z_le_x
              apply chs[J].reframe_xy_yz_post_zx x y z x_ne_y x_ne_z y_ne_z J_x_lt_z
                |>.mpr
              exact (chs.map f')[J].le_subst _ J_chs'_def chs'_z_le_x
          else
            constructor
            · intro chs_z_le_x
              apply
                (chs[i].reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ).symm
              apply chs[i].reframe_yx_yz_post_zx x y z x_ne_y x_ne_z y_ne_z |>.mp chs_z_le_x
            · intro chs'_z_le_x
              rw [chs[i].reframe_yx_yz_post_zx x y z x_ne_y x_ne_z y_ne_z]
              apply
                (chs.map f')[i].le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ)
              apply chs'_z_le_x
      )
  let x_in_C' : ⟨x, x_in_S⟩ ∈ ((swf (chs.map f')).sub {x, z}).C := by
    rw [ProtoOrder.C_def]
    intro b
    cases b with | mk b b_in_S =>
    rw [Set.mem_insert_iff] at b_in_S
    cases b_in_S with
    | inl h_eq =>
      rw [(swf (chs.map f')).sub_iff]
      simp [h_eq, Preorder.le_refl]
    | inr h_eq =>
      rw [Set.mem_singleton_iff] at h_eq
      rw [(swf (chs.map f')).sub_iff]
      rw [h_eq]
      exact chs'_x_lt_z.left
  let z_notin_C' : ⟨z, z_in_S⟩ ∉ ((swf (chs.map f')).sub {x, z}).C := by
    rw [ProtoOrder.C_def]
    intro wrong
    apply chs'_x_lt_z.right
    apply wrong ⟨x, x_in_S⟩
  let x_in_C : ⟨x, x_in_S⟩ ∈ ((swf chs).sub {x, z}).C :=
    C_eq_C'.symm ▸ x_in_C'
  let z_notin_C : ⟨z, z_in_S⟩ ∉ ((swf chs).sub {x, z}).C :=
    C_eq_C'.symm ▸ z_notin_C'

  let x_le_z : (swf chs).le x z := by
    let tmp := x_in_C ⟨z, z_in_S⟩
    simp at tmp
    exact tmp
  let not_z_le_x : ¬ (swf chs).le z x := by
    let tmp := z_notin_C
    rw [((swf chs).sub {x, z}).C_def] at tmp
    simp [not_forall] at tmp
    cases tmp with | intro x? h_x? =>
    cases h_x? with | intro x?_in_S h_x? =>
    cases x?_in_S with
    | inl h =>
      simp [h, Order.toPreorder, Preorder.toProtoOrder, LE.le] at h_x?
      exact h_x?
    | inr h =>
      simp [h, LE.le] at h_x?
      exfalso
      apply h_x?
      exact (swf chs).le_refl

  simp
  constructor
  · exact x_le_z
  · exact not_z_le_x


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
  let _f (i : chs.Idx) :=
    if h_i : J = i
    then chs[i].reframe_xy_yz z x y x_ne_z.symm y_ne_z.symm x_ne_y (h_i ▸ J_z_lt_y)
    else chs[i].reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z
  cases J with | mk J h_J =>
  let f' i (_O : Order α) := _f i

  let get_chs'_def (i : chs.Idx) : (chs.map f')[i.1] = _f i :=
    chs.getElem_map f' i

  let J_chs'_def
  : (chs.map f')[J] = chs[J].reframe_xy_yz z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y := by
    let tmp := get_chs'_def ⟨J, h_J⟩
    rw [tmp]
    simp
  let other_chs'_def
    (i : chs.Idx)
    (h_i_ne_J : i.1 ≠ J)
  : (chs.map f')[i.1] = chs[i].reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z := by
    rw [get_chs'_def i]
    simp
    intro i_def
    rw [Fin.mk_eq_mk] at i_def
    let _ := h_i_ne_J i_def.symm
    contradiction

  let J'_z_lt_x : (chs.map f')[J].lt z x := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_xy z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
  let J'_x_lt_y : (chs.map f')[J].lt x y := by
    rw [J_chs'_def]
    exact chs[J].reframe_xy_yz_post_yz z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
  -- let J'_z_lt_y : (chs.map f')[J].lt z y := by
  --   rw [J_chs'_def]
  --   constructor
  --   · exact chs[J].reframe_xy_yz_post_xz z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
  --     |>.mp J_z_lt_y.left
  --   · exact chs[J].reframe_xy_yz_post_zx z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
  --     |>.not.mp J_z_lt_y.right

  let O'_z_lt_x : ∀ (i : Set.compl {Fin.mk J h_J}), (chs.map f')[i.1].lt z x := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_zx_yx_post_zx x y z x_ne_y x_ne_z y_ne_z
  let O'_y_lt_x : ∀ (i : Set.compl {Fin.mk J h_J}), (chs.map f')[i.1].lt y x := by
    intro i
    let ⟨⟨i, h_i⟩, i_ne_J⟩ := i
    let h : i ≠ J := by
      intro h
      apply Set.mem_compl_singleton_iff.mp i_ne_J
      simp [h]
    let chs'_i_def := other_chs'_def ⟨i, h_i⟩ h
    apply Order.lt_subst _ _ chs'_i_def.symm
    apply chs[i].reframe_zx_yx_post_yx x y z x_ne_y x_ne_z y_ne_z

  let S : Set α := {z, y}
  let z_in_S : z ∈ S := Set.mem_insert z {y}
  let y_in_S : y ∈ S := Set.mem_insert_iff.mpr (Or.inr $ Set.mem_singleton y)
  let chs'_z_lt_y :=
    lemma_3_zy'
      swf (chs.map f') ⟨J, h_J⟩
      x y z
      J'_z_lt_x J'_x_lt_y
      O'_z_lt_x O'_y_lt_x
      aldec
      wpp

  let C_eq_C' :=
    iia
      chs (chs.map f') {z, y}
      (fun ⟨a, a_in_S⟩ ⟨b, b_in_S⟩ ⟨i, h_i⟩ => by
        simp at a_in_S b_in_S
        simp
        cases a_in_S <;> cases b_in_S
        case inl.inl h h' =>
          rw [h, h']
          simp [Preorder.le_refl]
        case inr.inr h h' =>
          rw [h, h']
          simp [Preorder.le_refl]
        case inl.inr h h' =>
          rw [h, h']
          if h_iJ : i = J then
            cases h_iJ
            constructor
            · intro chs_x_le_z
              apply Order.le_subst _ _ J_chs'_def.symm
              apply chs[J].reframe_xy_yz_post_xz z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
                |>.mp chs_x_le_z
            · intro chs'_x_le_z
              apply chs[J].reframe_xy_yz_post_xz z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
                |>.mpr
              exact (chs.map f')[J].le_subst _ J_chs'_def chs'_x_le_z
          else
            constructor
            · intro chs_z_le_y
              apply
                (chs[i].reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ).symm
              apply chs[i].reframe_zx_yx_post_zy x y z x_ne_y x_ne_z y_ne_z |>.mp chs_z_le_y
            · intro chs'_z_le_y
              rw [chs[i].reframe_zx_yx_post_zy x y z x_ne_y x_ne_z y_ne_z]
              apply
                (chs.map f')[i].le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ)
              apply chs'_z_le_y
        case inr.inl h h' =>
          rw [h, h']
          if h_iJ : i = J then
            cases h_iJ
            constructor
            · intro chs_z_le_x
              apply Order.le_subst _ _ J_chs'_def.symm
              apply chs[J].reframe_xy_yz_post_zx z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
                |>.mp chs_z_le_x
            · intro chs'_z_le_x
              apply chs[J].reframe_xy_yz_post_zx z x y x_ne_z.symm y_ne_z.symm x_ne_y J_z_lt_y
                |>.mpr
              exact (chs.map f')[J].le_subst _ J_chs'_def chs'_z_le_x
          else
            constructor
            · intro chs_y_le_z
              apply
                (chs[i].reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ).symm
              apply chs[i].reframe_zx_yx_post_yz x y z x_ne_y x_ne_z y_ne_z |>.mp chs_y_le_z
            · intro chs'_y_le_z
              rw [chs[i].reframe_zx_yx_post_yz x y z x_ne_y x_ne_z y_ne_z]
              apply
                (chs.map f')[i].le_subst
                  _ (other_chs'_def ⟨i, h_i⟩ h_iJ)
              apply chs'_y_le_z
      )
  let z_in_C' : ⟨z, z_in_S⟩ ∈ ((swf (chs.map f')).sub {z, y}).C := by
    rw [ProtoOrder.C_def]
    intro b
    cases b with | mk b b_in_S =>
    rw [Set.mem_insert_iff] at b_in_S
    cases b_in_S with
    | inl h_eq =>
      rw [(swf (chs.map f')).sub_iff]
      simp [h_eq, Preorder.le_refl]
    | inr h_eq =>
      rw [Set.mem_singleton_iff] at h_eq
      rw [(swf (chs.map f')).sub_iff]
      simp [h_eq, chs'_z_lt_y.left]
  let y_notin_C' : ⟨y, y_in_S⟩ ∉ ((swf (chs.map f')).sub {z, y}).C := by
    rw [ProtoOrder.C_def]
    intro wrong
    apply chs'_z_lt_y.right
    apply wrong ⟨z, z_in_S⟩
  let z_in_C : ⟨z, z_in_S⟩ ∈ ((swf chs).sub {z, y}).C :=
    C_eq_C'.symm ▸ z_in_C'
  let y_notin_C : ⟨y, y_in_S⟩ ∉ ((swf chs).sub {z, y}).C :=
    C_eq_C'.symm ▸ y_notin_C'

  let z_le_y : (swf chs).le z y := by
    let tmp := z_in_C ⟨y, y_in_S⟩
    simp at tmp
    exact tmp
  let not_y_le_z : ¬ (swf chs).le y z := by
    let tmp := y_notin_C
    rw [((swf chs).sub {z, y}).C_def] at tmp
    simp [not_forall] at tmp
    cases tmp with | intro z? h_z? =>
    cases h_z? with | intro z?_in_S h_z? =>
    cases z?_in_S with
    | inl h =>
      rw [(swf chs).sub_iff] at h_z?
      exact h ▸ h_z?
    | inr h =>
      rw [(swf chs).sub_iff, h] at h_z?
      exfalso
      apply h_z?
      exact (swf chs).le_refl

  simp
  constructor
  · exact z_le_y
  · exact not_y_le_z


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
  (x_ne_y : x ≠ y)
  (wpp : swf.Wpp)
  (iia : swf.Iia)
: ∀ (z : α),
  x ≠ z
  → y ≠ z
  → swf.almost_decisive {J} x y
  → swf.dictator J
:= fun z x_ne_z y_ne_z aldec_xy u v => by
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
