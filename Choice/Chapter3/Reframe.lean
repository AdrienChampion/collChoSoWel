import Choice.Chapter2



namespace Choice



-- section keep_xy_force_y_lt_z
--   abbrev Order.keep_xy_force_y_lt_z
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : Preorder α where
--     le a b :=
--       if a = x ∧ b = y then
--         O.le a b
--       else if a = y ∧ b = x then
--         O.le b a
--       else if a = y ∧ b = z then
--         True
--       else if a = z ∧ b = y then
--         False
--       else
--         a = b

--     toDecidableRel := by
--       simp [DecidableRel, LE.le]
--       intro a b
--       exact inferInstance
--     toDecidableEq := inferInstance

--     le_refl' a := by
--       simp [LE.le]
--       if h_ax : a = x then
--         simp [h_ax, x_ne_y]
--       else if h_ay : a = y then
--         simp [h_ay, x_ne_y.symm, y_ne_z]
--       else
--         simp [h_ax, h_ay]
    
--     le_trans' a b c := by
--       simp [LE.le]
--       if h_ax : a = x then
--         simp [h_ax, x_ne_y, x_ne_z]
--         if h_bx : b = x then
--           simp [h_bx, x_ne_y]
--           split
--           · intro ; assumption
--           · simp [x_ne_z]
--         else if h_by : b = y then
--           simp [h_bx, h_by, x_ne_y.symm, y_ne_z]
--           intro xy
--           split
--           case inl h_cx => simp [h_cx]
--           case inr h_cx =>
--             split
--             case inl h_cz =>
--               simp [h_cz]
--             sorry
--       else
--         sorry
      
-- end keep_xy_force_y_lt_z



section yx_yz
  abbrev Order.protoReframe_yx_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : Preorder α where
    le a b :=
      if a = x ∧ b = z then
        O.le x z
      else if a = z ∧ b = x then
        O.le z x
      else if a = y ∧ b = x then
        True
      else if a = x ∧ b = y then
        False
      else if a = y ∧ b = z then
        True
      else if a = z ∧ b = y then
        False
      else
        a = b
    toDecidableRel := by
      simp [DecidableRel, LE.le]
      intro a b
      exact inferInstance
    toDecidableEq := inferInstance

    le_refl' a := by
      simp [LE.le]
      if h_x : a = x then
        simp [h_x, x_ne_y, x_ne_z]
      else if h_y : a = y then
        simp [h_x, h_y, x_ne_y.symm, y_ne_z]
      else if h_z : a = z then
        simp [h_x, h_y, h_z, x_ne_z.symm, y_ne_z.symm]
      else
        simp [h_x, h_y, h_z]

    le_trans' a b c := by
      simp [LE.le]
      if h_ax : a = x then
        simp [h_ax, x_ne_y, x_ne_z]
        if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
          split
          case inl h_c => simp [h_c, x_ne_y, x_ne_z]
          split
          case inl h_c => simp [h_c, y_ne_z]
          split
          case inl h_c => simp [h_c]
          case inr h_c =>
            intro _ z_eq_c
            let _ := z_eq_c.symm
            contradiction
        else if h_bx : b = x then
          simp [h_bz, h_bx, x_ne_y, x_ne_z]
        else if h_by : b = y then
          simp [h_bz, h_bx, h_by, x_ne_y.symm, y_ne_z]
        else
          simp [h_bz, h_bx, h_by]
          intro x_eq_b
          let _ := x_eq_b.symm
          contradiction
      else if h_az : a = z then
        simp [h_ax, h_az, x_ne_z.symm, y_ne_z.symm]
        if h_bx : b = x then
          simp [h_bx, x_ne_z, x_ne_y]
          split
          case inl h_c => simp [h_c, y_ne_z.symm, x_ne_z.symm]
          split
          case inl h_c => simp [h_c, x_ne_y.symm, y_ne_z]
          split
          · intros
            assumption
          · intros _ x_eq_c
            let _ := x_eq_c.symm
            contradiction
        else if h_by : b = y then
          simp [h_by, y_ne_z, x_ne_y.symm]
        else if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
        else
          simp [*]
          intro z_eq_b
          let _ := z_eq_b.symm
          contradiction
      else if h_ay : a = y then
        simp [h_ax, h_az, h_ay, x_ne_y.symm, y_ne_z]
        if h_bx : b = x then
          simp [h_bx, x_ne_y, x_ne_z]
          split
          case inl h_c => simp [h_c]
          split
          case inl h_c => simp [h_c]
          split
          case inl h_c => simp [h_c]
          intro x_eq_c
          let _ := x_eq_c.symm
          contradiction
        else if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
          split
          case inl h_c => simp [h_c]
          split
          case inl h_c => simp [h_c]
          split
          case inl h_c => simp [h_c]
          intro z_eq_c
          let _ := z_eq_c.symm
          contradiction
        else if h_by : b = y then
          simp [h_by, x_ne_y.symm, y_ne_z]
        else
          simp [h_bx, h_bz, h_by]
          intro y_eq_b
          let _ := y_eq_b.symm
          contradiction
      else if h_az : a = z then
        simp [h_ax, h_ay, h_az, x_ne_z.symm, y_ne_z.symm]
        if h_bx : b = x then
          simp [h_bx, x_ne_y, x_ne_z]
          split
          case inl h_c => simp [h_c, x_ne_z.symm, y_ne_z.symm]
          split
          case inl h_c => simp [h_c]
          split
          case inl h_c => simp [h_c]
          intro _ x_eq_c
          let _ := x_eq_c.symm
          contradiction
        else if h_by : b = y then
          simp [h_by, x_ne_y.symm, y_ne_z]
        else if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
        else
          simp [h_bx, h_by, h_bz]
          intro z_eq_b
          let _ := z_eq_b.symm
          contradiction
      else
        simp [h_ax, h_ay, h_az]
        intro a_eq_b
        rw [← a_eq_b]
        simp [h_ax, h_ay, h_az]

  theorem Order.protoReframe_yx_yz_post_xz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le x z ↔ (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).le x z) := by
    simp [Preorder.toProtoOrder]

  theorem Order.protoReframe_yx_yz_post_zx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le z x ↔ (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).le z x) := by
    simp [Preorder.toProtoOrder, x_ne_z]

  theorem Order.protoReframe_yx_yz_post_yx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).lt y x := by
    simp [Preorder.toProtoOrder, x_ne_y.symm, y_ne_z]

  theorem Order.protoReframe_yx_yz_post_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).lt y z := by
    simp [Preorder.toProtoOrder, x_ne_y.symm, y_ne_z]

  abbrev Order.reframe_yx_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : Order α :=
    O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z
    |>.totalize

  theorem Order.reframe_yx_yz_post_xz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le x z ↔ (O.reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).le x z) := by
    -- simp [Order.toPreorder, Preorder.toProtoOrder, reframe]
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_xz :=
      (O.protoReframe_yx_yz_post_xz x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_zx :=
      (O.protoReframe_yx_yz_post_zx x y z x_ne_y x_ne_z y_ne_z)
    constructor
    · intro O_xz
      apply proto_sub_reframe x z _ |>.left
      exact proto_lemma_xz.mp O_xz
    · intro reframe_xz
      let _ := (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).toDecidableRel
      apply Decidable.byContradiction
      intro O_nxz
      let proto_nxz := proto_lemma_xz.not.mp O_nxz
      let O_zx : O.le z x := by
        cases O.le_total' z x
        · assumption
        · contradiction
      let proto_zx := proto_lemma_zx.mp O_zx
      let reframe_xz :=
        proto_sub_reframe z x proto_zx |>.right proto_nxz
      contradiction

  theorem Order.reframe_yx_yz_post_zx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le z x ↔ (O.reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).le z x) := by
    -- simp [Order.toPreorder, Preorder.toProtoOrder, reframe]
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_xz :=
      (O.protoReframe_yx_yz_post_xz x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_zx :=
      (O.protoReframe_yx_yz_post_zx x y z x_ne_y x_ne_z y_ne_z)
    constructor
    · intro O_zx
      apply proto_sub_reframe z x _ |>.left
      exact proto_lemma_zx.mp O_zx
    · intro reframe_zx
      let _ := (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).toDecidableRel
      apply Decidable.byContradiction
      intro O_nzx
      let proto_nzx := proto_lemma_zx.not.mp O_nzx
      let O_xz : O.le x z := by
        cases O.le_total' x z
        · assumption
        · contradiction
      let proto_xz := proto_lemma_xz.mp O_xz
      let reframe_xz :=
        proto_sub_reframe x z proto_xz |>.right proto_nzx
      contradiction

  theorem Order.reframe_yx_yz_post_yx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).lt y x := by
    let proto_y_lt_x :=
      O.protoReframe_yx_yz_post_yx x y z x_ne_y x_ne_z y_ne_z
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z)
    simp [ProtoOrder.lt_def]
    let h := proto_sub_reframe y x proto_y_lt_x.left
    apply And.intro h.left
    exact h.right proto_y_lt_x.right

  theorem Order.reframe_yx_yz_post_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z).lt y z := by
    let proto_y_lt_z :=
      O.protoReframe_yx_yz_post_yz x y z x_ne_y x_ne_z y_ne_z
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_yx_yz x y z x_ne_y x_ne_z y_ne_z)
    simp [ProtoOrder.lt_def]
    let h := proto_sub_reframe y z proto_y_lt_z.left
    apply And.intro h.left
    exact h.right proto_y_lt_z.right


  theorem Order.can_reframe_yx_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : ∃ (O' : Order α),
    (O.le x z ↔ O'.le x z)
    ∧ (O.le z x ↔ O'.le z x)
    ∧ O'.lt y x
    ∧ O'.lt y z
  := by
    let O' := O.reframe_yx_yz x y z x_ne_y x_ne_z y_ne_z
    exists O'
    constructor
    · exact O.reframe_yx_yz_post_xz x y z x_ne_y x_ne_z y_ne_z
    constructor
    · exact O.reframe_yx_yz_post_zx x y z x_ne_y x_ne_z y_ne_z
    constructor
    · exact O.reframe_yx_yz_post_yx x y z x_ne_y x_ne_z y_ne_z
    · exact O.reframe_yx_yz_post_yz x y z x_ne_y x_ne_z y_ne_z
end yx_yz



section xy_yz
  abbrev Order.protoReframe_xy_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : Preorder α where
    le a b :=
      if a = x ∧ b = z then
        O.le x z
      else if a = z ∧ b = x then
        O.le z x
      else if a = x ∧ b = y then
        True
      else if a = y ∧ b = x then
        False
      else if a = y ∧ b = z then
        True
      else if a = z ∧ b = y then
        False
      else
        a = b
    toDecidableRel := by
      simp [DecidableRel, LE.le]
      intro a b
      exact inferInstance
    toDecidableEq := inferInstance

    le_refl' a := by
      simp [LE.le]
      if h_x : a = x then
        simp [h_x, x_ne_y, x_ne_z]
      else if h_y : a = y then
        simp [h_x, h_y, x_ne_y.symm, y_ne_z]
      else if h_z : a = z then
        simp [h_x, h_y, h_z, x_ne_z.symm, y_ne_z.symm]
      else
        simp [h_x, h_y, h_z]

    le_trans' a b c := by
      simp [LE.le]
      if h_ax : a = x then
        simp [h_ax, x_ne_y, x_ne_z]
        if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
          split
          case inl h_c => simp [h_c, x_ne_y, x_ne_z]
          split
          case inl h_c => simp [h_c, y_ne_z]
          split
          case inl h_c => simp [h_c]
          case inr h_c =>
            intro _ z_eq_c
            let _ := z_eq_c.symm
            contradiction
        else if h_bx : b = x then
          simp [h_bz, h_bx, x_ne_y, x_ne_z]
        else if h_by : b = y then
          simp [h_bz, h_bx, h_by, x_ne_y.symm, y_ne_z]
          split ; intro ; contradiction
          case inr h_cx =>
            split
            · intro
              exact h.left
            case inr h_cz =>
              intro h_yc
              simp [h_yc]
        else
          simp [h_bz, h_bx, h_by]
          intro x_eq_b
          let _ := x_eq_b.symm
          contradiction
      else if h_az : a = z then
        simp [h_ax, h_az, x_ne_z.symm, y_ne_z.symm]
        if h_bx : b = x then
          simp [h_bx, x_ne_z, x_ne_y]
          split
          case inl h_c => simp [h_c, y_ne_z.symm, x_ne_z.symm]
          split
          case inl h_c =>
            intro h'
            exfalso
            apply h.right h'
          split
          · intros
            assumption
          · intros _ x_eq_c
            let _ := x_eq_c.symm
            contradiction
        else if h_by : b = y then
          simp [h_by, y_ne_z, x_ne_y.symm]
        else if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
        else
          simp [*]
          intro z_eq_b
          let _ := z_eq_b.symm
          contradiction
      else if h_ay : a = y then
        simp [h_ax, h_az, h_ay, x_ne_y.symm, y_ne_z]
        if h_bx : b = x then
          simp [h_bx, x_ne_y, x_ne_z]
        else if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
          split
          case inl h_c =>
            exact h.right
          split
          case inl h_c => simp [h_c]
          split
          case inl h_c => simp [h_c]
          intro z_eq_c
          let _ := z_eq_c.symm
          contradiction
        else if h_by : b = y then
          simp [h_by, x_ne_y.symm, y_ne_z]
        else
          simp [h_bx, h_bz, h_by]
          intro y_eq_b
          let _ := y_eq_b.symm
          contradiction
      else if h_az : a = z then
        simp [h_ax, h_ay, h_az, x_ne_z.symm, y_ne_z.symm]
        if h_bx : b = x then
          simp [h_bx, x_ne_y, x_ne_z]
          split
          case inl h_c => simp [h_c, x_ne_z.symm, y_ne_z.symm]
          split
          case inl h_c =>
            intro h'
            exfalso
            apply h.right h'
          split
          case inl h_c => simp [h_c]
          intro _ x_eq_c
          let _ := x_eq_c.symm
          contradiction
        else if h_by : b = y then
          simp [h_by, x_ne_y.symm, y_ne_z]
        else if h_bz : b = z then
          simp [h_bz, x_ne_z.symm, y_ne_z.symm]
        else
          simp [h_bx, h_by, h_bz]
          intro z_eq_b
          let _ := z_eq_b.symm
          contradiction
      else
        simp [h_ax, h_ay, h_az]
        intro a_eq_b
        rw [← a_eq_b]
        simp [h_ax, h_ay, h_az]

  theorem Order.protoReframe_xy_yz_post_xz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.le x z ↔ (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).le x z) := by
    simp [Preorder.toProtoOrder]

  theorem Order.protoReframe_xy_yz_post_zx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.le z x ↔ (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).le z x) := by
    simp [Preorder.toProtoOrder, x_ne_z]

  theorem Order.protoReframe_xy_yz_post_xy
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).lt x y := by
    simp [Preorder.toProtoOrder, x_ne_y.symm, y_ne_z]

  theorem Order.protoReframe_xy_yz_post_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).lt y z := by
    simp [Preorder.toProtoOrder, x_ne_z.symm, x_ne_y.symm, y_ne_z]

  abbrev Order.reframe_xy_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : Order α :=
    O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h
    |>.totalize

  theorem Order.reframe_xy_yz_post_xz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.le x z ↔ (O.reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).le x z) := by
    -- simp [Order.toPreorder, Preorder.toProtoOrder, reframe]
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h)
    let proto_lemma_xz :=
      (O.protoReframe_xy_yz_post_xz x y z x_ne_y x_ne_z y_ne_z h)
    let proto_lemma_zx :=
      (O.protoReframe_xy_yz_post_zx x y z x_ne_y x_ne_z y_ne_z h)
    constructor
    · intro O_xz
      apply proto_sub_reframe x z _ |>.left
      exact proto_lemma_xz.mp O_xz
    · intro reframe_xz
      let _ := (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).toDecidableRel
      apply Decidable.byContradiction
      intro O_nxz
      let proto_nxz := proto_lemma_xz.not.mp O_nxz
      let O_zx : O.le z x := by
        cases O.le_total' z x
        · assumption
        · contradiction
      let proto_zx := proto_lemma_zx.mp O_zx
      let reframe_xz :=
        proto_sub_reframe z x proto_zx |>.right proto_nxz
      contradiction

  theorem Order.reframe_xy_yz_post_zx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.le z x ↔ (O.reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).le z x) := by
    -- simp [Order.toPreorder, Preorder.toProtoOrder, reframe]
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h)
    let proto_lemma_xz :=
      (O.protoReframe_xy_yz_post_xz x y z x_ne_y x_ne_z y_ne_z h)
    let proto_lemma_zx :=
      (O.protoReframe_xy_yz_post_zx x y z x_ne_y x_ne_z y_ne_z h)
    constructor
    · intro O_zx
      apply proto_sub_reframe z x _ |>.left
      exact proto_lemma_zx.mp O_zx
    · intro reframe_zx
      let _ := (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).toDecidableRel
      apply Decidable.byContradiction
      intro O_nzx
      let proto_nzx := proto_lemma_zx.not.mp O_nzx
      let O_xz : O.le x z := by
        cases O.le_total' x z
        · assumption
        · contradiction
      let proto_xz := proto_lemma_xz.mp O_xz
      let reframe_xz :=
        proto_sub_reframe x z proto_xz |>.right proto_nzx
      contradiction

  theorem Order.reframe_xy_yz_post_xy
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).lt x y := by
    let proto_x_lt_y :=
      O.protoReframe_xy_yz_post_xy x y z x_ne_y x_ne_z y_ne_z h
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h)
    simp [ProtoOrder.lt_def]
    let h := proto_sub_reframe x y proto_x_lt_y.left
    apply And.intro h.left
    exact h.right proto_x_lt_y.right

  theorem Order.reframe_xy_yz_post_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : (O.reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h).lt y z := by
    let proto_y_lt_z :=
      O.protoReframe_xy_yz_post_yz x y z x_ne_y x_ne_z y_ne_z h
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h)
    simp [ProtoOrder.lt_def]
    let h := proto_sub_reframe y z proto_y_lt_z.left
    apply And.intro h.left
    exact h.right proto_y_lt_z.right


  theorem Order.can_reframe_xy_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
    (h : O.lt x z)
  : ∃ (O' : Order α),
    (O.le x z ↔ O'.le x z)
    ∧ (O.le z x ↔ O'.le z x)
    ∧ O'.lt x y
    ∧ O'.lt y z
  := by
    let O' := O.reframe_xy_yz x y z x_ne_y x_ne_z y_ne_z h
    exists O'
    constructor
    · exact O.reframe_xy_yz_post_xz x y z x_ne_y x_ne_z y_ne_z h
    constructor
    · exact O.reframe_xy_yz_post_zx x y z x_ne_y x_ne_z y_ne_z h
    constructor
    · exact O.reframe_xy_yz_post_xy x y z x_ne_y x_ne_z y_ne_z h
    · exact O.reframe_xy_yz_post_yz x y z x_ne_y x_ne_z y_ne_z h
section xy_yz



section zx_yx
  abbrev Order.protoReframe_zx_yx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : Preorder α where
    le a b :=
      if a = y ∧ b = z then
        O.le y z
      else if a = z ∧ b = y then
        O.le z y
      else if a = z ∧ b = x then
        True
      else if a = x ∧ b = z then
        False
      else if a = y ∧ b = x then
        True
      else if a = x ∧ b = y then
        False
      else
        a = b
    toDecidableRel := by
      simp [DecidableRel, LE.le]
      intro a b
      exact inferInstance
    toDecidableEq := inferInstance

    le_refl' a := by
      simp [LE.le]
      if h_x : a = x then
        simp [h_x, x_ne_y, x_ne_z]
      else if h_y : a = y then
        simp [h_x, h_y, x_ne_y.symm, y_ne_z]
      else if h_z : a = z then
        simp [h_x, h_y, h_z, x_ne_z.symm, y_ne_z.symm]
      else
        simp [h_x, h_y, h_z]

    le_trans' a b c := by
      simp [LE.le]
      if h_ax : a = x then
        rw [h_ax]
        simp [x_ne_y, x_ne_z]
        if h_bx : b = x then
          simp [h_bx, x_ne_z, x_ne_y]
        else if h_by : b = y then
          simp [h_bx, h_by]
        else if h_bz : b = z then
          simp [h_bx, h_by, h_bz]
        else
          simp [h_bx, h_by, h_bz]
          intro x_eq_b
          let _ := h_bx x_eq_b.symm
          contradiction
      else if h_ay : a = y then
        simp [h_ax, h_ay, x_ne_y, x_ne_y.symm, x_ne_z, y_ne_z]
        split
        case inl h_bz =>
          rw [h_bz]
          simp [y_ne_z.symm]
          split
          case inl h_cy =>
            rw [h_cy]
            simp [y_ne_z]
          case inr h_cy =>
            simp [x_ne_z.symm]
            split
            case inl h_cx =>
              rw [h_cx]
              simp [x_ne_z]
            case inr h_cx =>
              split
              · intros ; assumption
              case inr h_cz =>
                intro _ h_zc
                let _ := h_cz h_zc.symm
                contradiction
        case inr h_bz =>
          simp [h_bz]
          split
          case inl h_bx =>
            rw [h_bx]
            simp [x_ne_y, x_ne_z]
            split ; intro ; contradiction
            split ; intro ; contradiction
            intro h_xc
            simp [h_xc]
          case inr h_bx =>
            intro h_yb
            rw [h_yb.symm]
            simp [x_ne_y.symm]
      else if h_az : a = z then
        rw [h_az]
        simp [y_ne_z.symm]
        if h_bx : b = x then
          simp [h_az, h_bx, x_ne_z, x_ne_y]
          split ; intro ; contradiction
          split ; intro ; contradiction
          intro h ; rw [← h] ; simp [x_ne_z]
        else if h_by : b = y then
          simp [h_bx, h_by, y_ne_z, x_ne_y.symm, y_ne_z.symm, x_ne_z.symm]
          intro z_le_x
          simp [z_le_x]
          split
          case inl h_cz =>
            simp [h_cz, y_ne_z.symm]
          case inr h_cz =>
            split
            case inl h_cx =>
              rw [h_cx] ; simp [x_ne_y]
            case inr h_cx =>
              intro h_yc
              rw [← h_yc]
              simp
        else if h_bz : b = z then
          simp [h_bx, h_by, h_bz, y_ne_z.symm]
        else
          simp [h_bx, h_by, h_bz]
          intro h_zb
          let _ := h_bz h_zb.symm
          contradiction
      else
        simp [h_ax, h_ay, h_az]
        intro h_ab
        rw [← h_ab]
        simp [h_ax, h_ay, h_az]

  theorem Order.protoReframe_zx_yx_post_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le y z ↔ (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).le y z) := by
    simp [Preorder.toProtoOrder]

  theorem Order.protoReframe_zx_yx_post_zy
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le z y ↔ (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).le z y) := by
    simp [Preorder.toProtoOrder, y_ne_z.symm]

  theorem Order.protoReframe_zx_yx_post_zx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).lt z x := by
    simp [Preorder.toProtoOrder, x_ne_y, y_ne_z.symm, x_ne_z]

  theorem Order.protoReframe_zx_yx_post_yx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).lt y x := by
    simp [Preorder.toProtoOrder, x_ne_z, y_ne_z, x_ne_y]

  abbrev Order.reframe_zx_yx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : Order α :=
    O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z
    |>.totalize

  theorem Order.reframe_zx_yx_post_yz
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le y z ↔ (O.reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).le y z) := by
    -- simp [Order.toPreorder, Preorder.toProtoOrder]
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_yz :=
      (O.protoReframe_zx_yx_post_yz x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_zy :=
      (O.protoReframe_zx_yx_post_zy x y z x_ne_y x_ne_z y_ne_z)
    constructor
    · intro O_yz
      apply proto_sub_reframe y z _ |>.left
      exact proto_lemma_yz.mp O_yz
    · intro reframe_yz
      let _ := (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).toDecidableRel
      apply Decidable.byContradiction
      intro O_nyz
      let proto_nyz := proto_lemma_yz.not.mp O_nyz
      let O_zy : O.le z y := by
        cases O.le_total' z y
        · assumption
        · contradiction
      let proto_zy := proto_lemma_zy.mp O_zy
      let reframe_zy :=
        proto_sub_reframe z y proto_zy |>.right proto_nyz
      contradiction

  theorem Order.reframe_zx_yx_post_zy
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.le z y ↔ (O.reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).le z y) := by
    -- simp [Order.toPreorder, Preorder.toProtoOrder, reframe]
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_zy :=
      (O.protoReframe_zx_yx_post_zy x y z x_ne_y x_ne_z y_ne_z)
    let proto_lemma_yz :=
      (O.protoReframe_zx_yx_post_yz x y z x_ne_y x_ne_z y_ne_z)
    constructor
    · intro O_zy
      apply proto_sub_reframe z y _ |>.left
      exact proto_lemma_zy.mp O_zy
    · intro reframe_zx
      let _ := (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).toDecidableRel
      apply Decidable.byContradiction
      intro O_nzy
      let proto_nzy := proto_lemma_zy.not.mp O_nzy
      let O_xz : O.le y z := by
        cases O.le_total' y z
        · assumption
        · contradiction
      let proto_yz := proto_lemma_yz.mp O_xz
      let reframe_yz :=
        proto_sub_reframe y z proto_yz |>.right proto_nzy
      contradiction

  theorem Order.reframe_zx_yx_post_zx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).lt z x := by
    let proto_z_lt_x :=
      O.protoReframe_zx_yx_post_zx x y z x_ne_y x_ne_z y_ne_z
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z)
    simp [ProtoOrder.lt_def]
    let h := proto_sub_reframe z x proto_z_lt_x.left
    apply And.intro h.left
    exact h.right proto_z_lt_x.right

  theorem Order.reframe_zx_yx_post_yx
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : (O.reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z).lt y x := by
    let proto_y_lt_x :=
      O.protoReframe_zx_yx_post_yx x y z x_ne_y x_ne_z y_ne_z
    let proto_sub_reframe := Preorder.totalize_subrel
      (O.protoReframe_zx_yx x y z x_ne_y x_ne_z y_ne_z)
    simp [ProtoOrder.lt_def]
    let h := proto_sub_reframe y x proto_y_lt_x.left
    apply And.intro h.left
    exact h.right proto_y_lt_x.right


  theorem Order.can_reframe'
    [Finite α]
    (O : Order α)
    (x y z : α)
    (x_ne_y : x ≠ y)
    (x_ne_z : x ≠ z)
    (y_ne_z : y ≠ z)
  : ∃ (O' : Order α),
    (O.le y z ↔ O'.le y z)
    ∧ (O.le z y ↔ O'.le z y)
    ∧ O'.lt z x
    ∧ O'.lt y x
  := by
    let O' := O.reframe_zx_yx x y z x_ne_y x_ne_z y_ne_z
    exists O'
    constructor
    · exact O.reframe_zx_yx_post_yz x y z x_ne_y x_ne_z y_ne_z
    constructor
    · exact O.reframe_zx_yx_post_zy x y z x_ne_y x_ne_z y_ne_z
    constructor
    · exact O.reframe_zx_yx_post_zx x y z x_ne_y x_ne_z y_ne_z
    · exact O.reframe_zx_yx_post_yx x y z x_ne_y x_ne_z y_ne_z
end zx_yx



-- section zx_xy
--   abbrev Order.protoReframe_zx_xy
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--     (h : O.lt z y)
--   : Preorder α where
--     le a b :=
--       if a = y ∧ b = z then
--         O.le y z
--       else if a = z ∧ b = y then
--         O.le z y
--       else if a = z ∧ b = x then
--         True
--       else if a = x ∧ b = z then
--         False
--       else if a = x ∧ b = y then
--         True
--       else if a = y ∧ b = x then
--         False
--       else
--         a = b
--     toDecidableRel := by
--       simp [DecidableRel, LE.le]
--       intro a b
--       exact inferInstance
--     toDecidableEq := inferInstance

--     le_refl' a := by
--       simp [LE.le]
--       if h_x : a = x then
--         simp [h_x, x_ne_y, x_ne_z]
--       else if h_y : a = y then
--         simp [h_x, h_y, x_ne_y.symm, y_ne_z]
--       else if h_z : a = z then
--         simp [h_x, h_y, h_z, x_ne_z.symm, y_ne_z.symm]
--       else
--         simp [h_x, h_y, h_z]

--     le_trans' a b c := by
--       simp [LE.le]
--       if h_ax : a = x then
--         rw [h_ax]
--         simp [x_ne_y, x_ne_z]
--         if h_bx : b = x then
--           simp [h_bx, x_ne_z, x_ne_y]
--         else if h_by : b = y then
--           simp [h_bx, h_by]
--         else if h_bz : b = z then
--           simp [h_bx, h_by, h_bz]
--         else
--           simp [h_bx, h_by, h_bz]
--           intro x_eq_b
--           let _ := h_bx x_eq_b.symm
--           contradiction
--       else if h_ay : a = y then
--         simp [h_ax, h_ay, x_ne_y, x_ne_y.symm, x_ne_z, y_ne_z]
--         split
--         case inl h_bz =>
--           rw [h_bz]
--           simp [y_ne_z.symm]
--           split
--           case inl h_cy =>
--             rw [h_cy]
--             simp [y_ne_z]
--           case inr h_cy =>
--             simp [x_ne_z.symm]
--             split
--             case inl h_cx =>
--               rw [h_cx]
--               simp [x_ne_z]
--             case inr h_cx =>
--               split
--               · intros ; assumption
--               case inr h_cz =>
--                 intro _ h_zc
--                 let _ := h_cz h_zc.symm
--                 contradiction
--         case inr h_bz =>
--           simp [h_bz]
--           split
--           case inl h_bx =>
--             rw [h_bx]
--             simp [x_ne_y, x_ne_z]
--             split ; intro ; contradiction
--             split ; intro ; contradiction
--             intro h_xc
--             simp [h_xc]
--           case inr h_bx =>
--             intro h_yb
--             rw [h_yb.symm]
--             simp [x_ne_y.symm]
--       else if h_az : a = z then
--         rw [h_az]
--         simp [y_ne_z.symm]
--         if h_bx : b = x then
--           simp [h_az, h_bx, x_ne_z, x_ne_y]
--           split ; intro ; contradiction
--           split ; intro ; contradiction
--           intro h ; rw [← h] ; simp [x_ne_z]
--         else if h_by : b = y then
--           simp [h_bx, h_by, y_ne_z, x_ne_y.symm, y_ne_z.symm, x_ne_z.symm]
--           intro z_le_x
--           simp [z_le_x]
--           split
--           case inl h_cz =>
--             simp [h_cz, y_ne_z.symm]
--           case inr h_cz =>
--             split
--             case inl h_cx =>
--               rw [h_cx] ; simp [x_ne_y]
--             case inr h_cx =>
--               intro h_yc
--               rw [← h_yc]
--               simp
--         else if h_bz : b = z then
--           simp [h_bx, h_by, h_bz, y_ne_z.symm]
--         else
--           simp [h_bx, h_by, h_bz]
--           intro h_zb
--           let _ := h_bz h_zb.symm
--           contradiction
--       else
--         simp [h_ax, h_ay, h_az]
--         intro h_ab
--         rw [← h_ab]
--         simp [h_ax, h_ay, h_az]

--   theorem Order.protoReframe_zx_xy_post_yz
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.le y z ↔ (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).le y z) := by
--     simp [Preorder.toProtoOrder]

--   theorem Order.protoReframe_zx_xy_post_zy
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.le z y ↔ (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).le z y) := by
--     simp [Preorder.toProtoOrder, y_ne_z.symm]

--   theorem Order.protoReframe_zx_xy_post_zx
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).lt z x := by
--     simp [Preorder.toProtoOrder, x_ne_y, y_ne_z.symm, x_ne_z]

--   theorem Order.protoReframe_zx_xy_post_yx
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).lt y x := by
--     simp [Preorder.toProtoOrder, x_ne_z, y_ne_z, x_ne_y]

--   abbrev Order.reframe_zx_xy
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : Order α :=
--     O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z
--     |>.totalize

--   theorem Order.reframe_zx_xy_post_yz
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.le y z ↔ (O.reframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).le y z) := by
--     -- simp [Order.toPreorder, Preorder.toProtoOrder]
--     let proto_sub_reframe := Preorder.totalize_subrel
--       (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z)
--     let proto_lemma_yz :=
--       (O.protoReframe_zx_xy_post_yz x y z x_ne_y x_ne_z y_ne_z)
--     let proto_lemma_zy :=
--       (O.protoReframe_zx_xy_post_zy x y z x_ne_y x_ne_z y_ne_z)
--     constructor
--     · intro O_yz
--       apply proto_sub_reframe y z _ |>.left
--       exact proto_lemma_yz.mp O_yz
--     · intro reframe_yz
--       let _ := (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).toDecidableRel
--       apply Decidable.byContradiction
--       intro O_nyz
--       let proto_nyz := proto_lemma_yz.not.mp O_nyz
--       let O_zy : O.le z y := by
--         cases O.le_total' z y
--         · assumption
--         · contradiction
--       let proto_zy := proto_lemma_zy.mp O_zy
--       let reframe_zy :=
--         proto_sub_reframe z y proto_zy |>.right proto_nyz
--       contradiction

--   theorem Order.reframe_zx_xy_post_zy
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.le z y ↔ (O.reframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).le z y) := by
--     -- simp [Order.toPreorder, Preorder.toProtoOrder, reframe]
--     let proto_sub_reframe := Preorder.totalize_subrel
--       (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z)
--     let proto_lemma_zy :=
--       (O.protoReframe_zx_xy_post_zy x y z x_ne_y x_ne_z y_ne_z)
--     let proto_lemma_yz :=
--       (O.protoReframe_zx_xy_post_yz x y z x_ne_y x_ne_z y_ne_z)
--     constructor
--     · intro O_zy
--       apply proto_sub_reframe z y _ |>.left
--       exact proto_lemma_zy.mp O_zy
--     · intro reframe_zx
--       let _ := (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).toDecidableRel
--       apply Decidable.byContradiction
--       intro O_nzy
--       let proto_nzy := proto_lemma_zy.not.mp O_nzy
--       let O_xz : O.le y z := by
--         cases O.le_total' y z
--         · assumption
--         · contradiction
--       let proto_yz := proto_lemma_yz.mp O_xz
--       let reframe_yz :=
--         proto_sub_reframe y z proto_yz |>.right proto_nzy
--       contradiction

--   theorem Order.reframe_zx_xy_post_zx
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.reframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).lt z x := by
--     let proto_z_lt_x :=
--       O.protoReframe_zx_xy_post_zx x y z x_ne_y x_ne_z y_ne_z
--     let proto_sub_reframe := Preorder.totalize_subrel
--       (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z)
--     simp [ProtoOrder.lt_def]
--     let h := proto_sub_reframe z x proto_z_lt_x.left
--     apply And.intro h.left
--     exact h.right proto_z_lt_x.right

--   theorem Order.reframe_zx_xy_post_yx
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : (O.reframe_zx_xy x y z x_ne_y x_ne_z y_ne_z).lt y x := by
--     let proto_y_lt_x :=
--       O.protoReframe_zx_xy_post_yx x y z x_ne_y x_ne_z y_ne_z
--     let proto_sub_reframe := Preorder.totalize_subrel
--       (O.protoReframe_zx_xy x y z x_ne_y x_ne_z y_ne_z)
--     simp [ProtoOrder.lt_def]
--     let h := proto_sub_reframe y x proto_y_lt_x.left
--     apply And.intro h.left
--     exact h.right proto_y_lt_x.right


--   theorem Order.can_reframe'
--     [Finite α]
--     (O : Order α)
--     (x y z : α)
--     (x_ne_y : x ≠ y)
--     (x_ne_z : x ≠ z)
--     (y_ne_z : y ≠ z)
--   : ∃ (O' : Order α),
--     (O.le y z ↔ O'.le y z)
--     ∧ (O.le z y ↔ O'.le z y)
--     ∧ O'.lt z x
--     ∧ O'.lt y x
--   := by
--     let O' := O.reframe_zx_xy x y z x_ne_y x_ne_z y_ne_z
--     exists O'
--     constructor
--     · exact O.reframe_zx_xy_post_yz x y z x_ne_y x_ne_z y_ne_z
--     constructor
--     · exact O.reframe_zx_xy_post_zy x y z x_ne_y x_ne_z y_ne_z
--     constructor
--     · exact O.reframe_zx_xy_post_zx x y z x_ne_y x_ne_z y_ne_z
--     · exact O.reframe_zx_xy_post_yx x y z x_ne_y x_ne_z y_ne_z
-- end zx_xy

