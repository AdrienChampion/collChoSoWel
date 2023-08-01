import Choice.Chapter1.Section2



/-! # Section 1.3 -/
namespace Choice



/-! ### Lemma `1*a` -/
section lemma_1_a
  variable
    {R : Rel α}
    [I : R.PreOrder]
    {x y z : α} [R.InDom x] [R.InDom y] [R.InDom z]

  theorem Rel.PreOrder.trans_I : R.I x y → R.I y z → R.I x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      I.trans h_yz.right h_xy.right
    ⟩

  theorem Rel.PreOrder.trans_PI : R.P x y → R.I y z → R.P x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      fun h_zx => h_xy.right $ I.trans h_yz.left h_zx
    ⟩

  theorem Rel.PreOrder.trans_IP : R.I x y → R.P y z → R.P x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      fun h_zx => h_yz.right $ I.trans h_zx h_xy.left
    ⟩
  
  theorem Rel.PreOrder.trans_P : R.P x y → R.P y z → R.P x z :=
    fun h_xy h_yz => ⟨
      I.trans h_xy.left h_yz.left,
      fun h_zx => h_yz.right $ I.trans h_zx h_xy.left
    ⟩
end lemma_1_a



/-! ### Lemma `1*b` -/
section lemma_1_b
  variable
    {R : Rel α}
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]

  -- def Rel.getMax : α :=
  --   aux R.default R.listDom
  -- where
  --   aux (a : α) [R.InDom a] (l : List α) (h : l.all fun a => a ∈ R) : List α → α
  --   | [] => a
  --   | head::tail =>
  --     let a :=
  --       if R.P head a then head else a
  --     aux a tail

  -- theorem Rel.getMax_in_Dom : R.getMax ∈ R := by
  --   simp [Membership.mem]

  -- theorem Rel.getMax_is_max : R.getMax ∈ R.M := by
  --   simp [Membership.mem, M]
  --   sorry


  -- /-- Original version does not require the domaine to be non-empty... -/
  -- theorem Rel.PreOrder.finite_dom_has_max
  -- : ∃ (a : α), R.max a := by
  --   let list := R.listDom
  --   sorry
end lemma_1_b