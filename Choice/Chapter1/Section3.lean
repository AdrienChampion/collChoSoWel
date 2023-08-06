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
  def Rel.listMaxP
    (R : Rel α)
    (l : List α)
    (_h_nempty : l ≠ [])
  : α :=
    match l with
    | [max] => max
    | hd::hd'::tl =>
      let max := R.listMaxP (hd'::tl) (List.cons_ne_nil _ _)
      if R.P hd max then hd else max

  theorem Rel.listMaxP_in_list
    (R : Rel α)
    (l : List α)
    (h_nempty : l ≠ [])
  : (R.listMaxP l h_nempty) ∈ l :=
    match l with
    | [max] => by
      simp only [listMaxP, Membership.mem, List.Mem.head]
    | hd::hd'::tl => by
      let ih :=
        R.listMaxP_in_list (hd'::tl) (List.cons_ne_nil _ _)
      unfold listMaxP
      simp [Membership.mem]
      split
      · exact List.Mem.head (hd'::tl)
      · apply List.Mem.tail
        exact ih

  theorem Rel.listMaxP_max
    (R : Rel α)
    [R.PreOrder]
    (l : List α)
    (h_nempty : l ≠ [])
    (a : α)
    (h_a_dom : a ∈ l)
    (allInDom : (a : α) → a ∈ l → R.InDom a)
  : ¬ R.P a (R.listMaxP l h_nempty) :=
    let h_a_in_dom :=
      allInDom a h_a_dom
    match l with
    | [max] => by
      let h_a_eq : a = max := by
        cases h_a_dom ; rfl ; contradiction
      simp [h_a_eq, listMaxP, R.P_irrefl]
    | hd::hd'::tl => by
      let hd_in_dom :=
        allInDom hd (List.Mem.head (hd'::tl))
      unfold listMaxP ; simp only []
      let sub_in_dom :=
        let inList' := R.listMaxP_in_list (hd'::tl) (List.cons_ne_nil _ _)
        allInDom _ (List.Mem.tail hd inList')
      split <;> cases h_a_dom
      · intro h
        exact h.right h.left
      case inl.tail h_hd_P_sub h_a_dom =>
        let h_not_a_P_sub :=
          R.listMaxP_max (hd'::tl) (List.cons_ne_nil _ _) a h_a_dom
            (fun a h => allInDom a $ List.Mem.tail hd h)
        intro h_a_P_hd
        apply h_not_a_P_sub
        apply R.P.trans hd h_a_P_hd h_hd_P_sub
      · assumption
      case inr.tail h_hd_P_sub h_a_dom =>
        apply R.listMaxP_max (hd'::tl) (List.cons_ne_nil _ _) a h_a_dom
          (fun a h => allInDom a $ List.Mem.tail hd h)

  def Rel.getMax
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : α :=
    R.listMaxP R.listDom R.nemptyListDom
  
  instance Rel.getMax_InDom
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : R.InDom R.getMax :=
    let h := R.listMaxP_in_list R.listDom R.nemptyListDom
    Rel.InDom.ofInList h

  /-- Closest equivalent to lemma 1.b.
  
  Original formulation omits the necessary assumption that `R.Dom ≠ ∅`. -/
  theorem Rel.getMax_max
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : R.max R.getMax := by
    simp only [Rel.M, Membership.mem, max]
    apply And.intro R.getMax_InDom
    intro a instInDom_a
    apply R.listMaxP_max R.listDom R.nemptyListDom a instInDom_a.toInList
      (fun _ h_a_dom => InDom.ofInList h_a_dom)



  /- Lemma 1.b.
  
  Original formulation omits the necessary assumption that `R.Dom ≠ ∅`. -/
  theorem Rel.lemma_1_b
    {R : Rel α}
    [R.PreOrder]
    [Set.Finite R.Dom]
    [Set.NEmpty R.Dom]
  : R.max R.getMax :=
    R.getMax_max
end lemma_1_b



section lemma_1_c
  theorem Rel.lemma_1_c_mp₁
    (R : Rel α)
    [R.Refl]
    {a a' : α} [aInDom : R.InDom a] [R.InDom a']
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
  : R.P a a' → R.C a := by
    intro h_a_P_a'
    apply And.intro aInDom
    intro x xInDom
    cases h_Dom x with
    | inl h_eq =>
      rw [h_eq]
      exact R.refl
    | inr h_eq =>
      rw [h_eq]
      exact h_a_P_a'.left

  theorem Rel.lemma_1_c_mp₂
    (R : Rel α)
    {a a' : α} [R.InDom a] [R.InDom a']
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
  : R.P a a' → ((x : α) → [R.InDom x] → R.C x → x = a) := by
    intro h_a_P_a' x xInDom h_x_max
    cases h_Dom x
    case inl _ =>
      assumption
    case inr h_eq =>
      let h_not_a_R_a' := h_a_P_a'.right
      let h_a_R_a' := h_eq ▸ h_x_max.right a
      contradiction

  theorem Rel.lemma_1_c_mpr
    (R : Rel α)
    [R.Refl]
    [Set.Finite R.Dom]
    {a a' : α} [R.InDom a] [a'InDom : R.InDom a']
    (h_ne : a ≠ a')
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
    (h₁ : R.C a)
    (h₂ : (x : α) → [R.InDom x] → R.C x → x = a)
  : R.P a a' := by
    simp
    apply And.intro $ h₁.right a'
    intro h_a'_R_a
    let h : R.C a' := by
      apply And.intro a'InDom
      intro x xInDom
      cases h_Dom x
      case inl h_eq => rw [h_eq] ; exact h_a'_R_a
      case inr h_eq => rw [h_eq] ; exact R.refl
    rw [h₂ a' h] at h_ne
    contradiction

  /-- Lemma 1.c.

  Assumption `h_ne` is not in the book, but it is necessary for the theorem's `Iff.mpr`, since `R.P`
  is not reflexive. The book version uses `[x, y]` for the set composed of `x` and `y`, which maybe
  indicates that `x` and `y` should be different. -/
  theorem Rel.lemma_1_c
    (R : Rel α)
    [R.Refl]
    [Set.Finite R.Dom]
    {a a' : α} [R.InDom a] [R.InDom a']
    (h_ne : a ≠ a')
    (h_Dom : (x : α) → [R.InDom x] → x = a ∨ x = a')
  : R.P a a' ↔ ( R.C a ∧ ((x : α) → [R.InDom x] → R.C x → x = a)) := by
    constructor
    · intro h_a_P_a'
      constructor
      · apply R.lemma_1_c_mp₁ h_Dom h_a_P_a'
      · apply R.lemma_1_c_mp₂ h_Dom h_a_P_a'
    · intro conj
      let ⟨h_C_a, h⟩ := conj
      apply R.lemma_1_c_mpr h_ne h_Dom h_C_a h
end lemma_1_c



section lemma_1_d
  /-- Lemma 1.d. -/
  theorem Rel.lemma_1_d
    (R : Rel α)
    [R.PreOrder]
    (best : α)
    [R.InDom best]
    (h_best : best ∈ R.C)
  : ∀ (a : α), [R.InDom a] → R.C a ↔ R.M a := by
    intro aMax aMaxInDom
    constructor
    · exact R.max_of_best aMax -- `aMax` is actually a *best* here, not a *max*
    · simp only [M, C]
      unfold Rel.max
      unfold Rel.best
      intro h_Max
      let h_aMax_R_best : R aMax best := by
        let h_best_R_aMax :=
          h_best.right aMax
        let h_not_best_P_aMax :=
          h_Max.right best
        simp [P] at h_not_best_P_aMax
        exact h_not_best_P_aMax h_best_R_aMax |> Decidable.not_not.mp
      apply And.intro aMaxInDom
      intro y yInDom
      apply R.trans (a' := best) h_aMax_R_best $ h_best.right y

  theorem Rel.lemma_1_d_C_empty
    (R : Rel α)
    [R.PreOrder]
    (h_diff : ¬ ∀ (a : α), [R.InDom a] → R.C a ↔ R.M a)
  : ¬ ∃ (best : α), R.InDom best ∧ R.C best :=
    fun ⟨best, _bestInDom, h_C_best⟩ =>
      R.lemma_1_d best h_C_best
      |> h_diff
end lemma_1_d



section lemma_1_e
  variable
    {α : Type u}

  /-- Dependent `P`-chain.

  Input `hd : α` is the head of the chain. The chain itself represents a path from `hd` to (one of)
  its `R.max`(s). -/
  inductive Rel.PChainD (R : Rel α) : α → Type u
  | max : ∀ {a : α}, a ∈ R.M → R.PChainD a
  | cons : ∀ {a : α} (b : α),
    [R.InDom a] → [R.InDom b] → R.P b a → R.PChainD b → R.PChainD a

  /-- Encodes that `x` appears in a `PChain`, based on `List.Mem`.
  
  Used for encoding and defining `Membership α R.PChain`. -/
  inductive Rel.PChainD.Mem
    {R : Rel α}
    (x : α)
  : {hd : α} → R.PChainD hd → Prop
  | max (h : x ∈ R.M) : Mem x (PChainD.max h)
  | head [R.InDom x] (b : α) [R.InDom b] (h : R.P b x) (tail : R.PChainD b)
    : Mem x (PChainD.cons b h tail)
  | tail (a b : α) [R.InDom a] [R.InDom b] (h : R.P b a) (tail : R.PChainD b)
    : Mem x tail → Mem x (PChainD.cons b h tail)

  instance {R : Rel α} {hd : α} : Membership α (R.PChainD hd) where
    mem (x : α) := Rel.PChainD.Mem x (hd := hd)


  /-- Same as `PChainD` but erases the chain's head from the type parameters. -/
  structure Rel.PChain (R : Rel α) : Type u where
    hd : α
    dep : R.PChainD hd

  /-- Same as `PChainD.Mem` but erases the chain's head from the type parameters.
  
  Used for encoding and defining `Membership α R.PChain`. -/
  abbrev Rel.PChain.Mem
    {R : Rel α}
    (x : α)
    (chain : R.PChain)
  : Prop :=
    PChainD.Mem x chain.dep

  instance
    {R : Rel α}
  : Membership α R.PChain where
    mem := Rel.PChain.Mem



  section
    variable
      {α : Type u}
      {R : Rel α}

    namespace Rel.PChainD
      def len : R.PChainD hd → Nat
      | max _ => 1
      | cons _ _ tail => 1 + tail.len

      def zero_lt_len : (chain : R.PChainD hd) → 0 < chain.len
      | max _ => Nat.zero_lt_succ _
      | cons b h tail => by
        simp [len, ←Nat.succ_eq_one_add]
        apply Nat.zero_lt_succ
      
      def len_ne_zero (chain : R.PChainD hd) : chain.len ≠ 0 :=
        Nat.not_eq_zero_of_lt chain.zero_lt_len



      theorem all_in_dom
        {hd : α}
        (chain : R.PChainD hd)
        (elm : α)
      : elm ∈ chain → R.InDom elm
      | Mem.max h => h.left
      | Mem.head _b _h _tail => inferInstance
      | Mem.tail _hd _b _h tail elm_in_tail =>
        tail.all_in_dom elm elm_in_tail

      theorem subset_listDom
        [Set.Finite R.Dom]
        (chain : R.PChainD hd)
      : ∀ (a : α), a ∈ chain → a ∈ R.listDom := fun a a_in_chain =>
        chain.all_in_dom a a_in_chain
        |> R.listDomIso.mpr

      theorem head_in_dom
        {hd : α}
      : (chain : R.PChainD hd) → hd ∈ chain
      | max h => Mem.max h
      | cons b h tail => Mem.head b h tail

      def getMax
        {hd : α}
      : R.PChainD hd → α
      | max _h_M_hd => hd
      | cons _ _ tail =>
        getMax tail

      theorem getMax_cons
        {a b : α} [R.InDom a] [R.InDom b]
        {h : R.P b a}
        {tail : R.PChainD b}
      : (Rel.PChainD.cons b h tail).getMax = tail.getMax :=
        rfl

      theorem getMax_is_max
        {hd : α}
      : (chain : R.PChainD hd) → chain.getMax ∈ R.M
      | max h => h
      | cons _ _ tail => by
        rw [getMax_cons]
        exact getMax_is_max tail

      theorem getMax_in_chain
        {hd : α}
      : (chain : R.PChainD hd) → chain.getMax ∈ chain
      | max h => by
        exact Mem.max h
      | cons b h_b_P_a tail => by
        rw [getMax_cons]
        apply Mem.tail
        exact getMax_in_chain tail
      
      theorem getMax_InDom
        {hd : α}
      : (chain : R.PChainD hd) → R.InDom chain.getMax :=
        fun chain =>
          chain.getMax_is_max.left

      theorem getMax_R_all
        [R.PreOrder]
        {hd : α}
        (chain : R.PChainD hd)
      : ∀ (elm : α), elm ∈ chain → R chain.getMax elm := by
        -- needed for typeclass resolution in the `head` case
        let _maxInDom := chain.getMax_InDom
        intro elm h_elm_in_chain
        cases h_elm_in_chain with
        | max h_max =>
          simp [getMax]
          let hdInDom := h_max.left
          exact R.refl
        | head b h_b_P_hd tail =>
          apply R.trans b
          apply tail.getMax_R_all
          apply tail.head_in_dom
          apply h_b_P_hd.left
        | tail a b h tail =>
          rw [getMax_cons]
          apply getMax_R_all
          assumption
      
      theorem getMax_R_head
        [R.PreOrder]
        {hd : α}
        (chain : R.PChainD hd)
      : R chain.getMax hd :=
        chain.getMax_R_all hd chain.head_in_dom

      theorem not_in_chain
        [R.PreOrder]
        {a b : α} [R.InDom a] [R.InDom b]
        (h_b_P_a : R.P b a)
        (chain : R.PChainD b)
      : ¬ a ∈ chain := by
        intro a_in_cons
        cases a_in_cons with
        | max _ =>
          exact h_b_P_a.right h_b_P_a.left
        | head _ _ _ =>
          exact h_b_P_a.right h_b_P_a.left
        | tail b c h_c_P_b tail =>
          let h_c_P_a :=
            R.P.trans b h_c_P_b h_b_P_a
          apply not_in_chain h_c_P_a tail
          assumption


      
      -- theorem len_tail
      --   [R.PreOrder]
      --   [Set.Finite R.Dom]
      --   (a b : α) [R.InDom a] [R.InDom b]
      --   (h_b_P_a : R.P b a)
      --   (tail : R.PChainD b)
      --   (chain : R.PChainD a)
      -- : chain = cons b h_b_P_a tail → tail.len < R.listDom.length := by
      --   intro h_chain_def
      --   let h :=
      --     tail.not_in_chain h_b_P_a
      --   let a_in_listDom : a ∈ R.listDom :=
      --     R.listDomIso.mpr inferInstance

      --   sorry
      
      -- theorem iso_listDom_of_max_len_mpr
      --   [Set.Finite R.Dom]
      --   (chain : R.PChainD hd)
      -- : chain.len = R.listDom.length → ∀ (a : α), a ∈ R.listDom → a ∈ chain := by
      --   intro h_len a a_in_listDom
      --   sorry



      /-- How do I prove this? `/(-_-)\` -/
      theorem len_le_listDom_len
        [Set.Finite R.Dom]
        (chain : R.PChainD hd)
      : chain.len ≤ R.listDom.length := by
        apply Decidable.byContradiction
        intro h
        simp [Nat.lt_of_not_le] at h
        sorry
    end Rel.PChainD
  end



  theorem Rel.lemma_1_e_mpr
    (R : Rel α)
    [R.PreOrder]
    [Set.Finite R.Dom]
  : (∀ (a : α), [R.InDom a] → R.C a ↔ R.M a)
  → (x y : α) → [R.InDom x] → [R.InDom y]
  → R.M x → R.M y
  → R.I x y := fun h_C_eq_M x y _ _ h_Max_x h_Max_y =>
    let h_C_x :=
      (h_C_eq_M x).mpr h_Max_x
    let h_C_y :=
      (h_C_eq_M y).mpr h_Max_y
    ⟨h_C_x.right y, h_C_y.right x⟩


  -- /-- This is true on finite domains but writing the proof is hard for me. -/
  -- theorem Rel.tmp
  --   (R : Rel α)
  --   [R.PreOrder]
  --   [Set.Finite R.Dom]
  --   [Set.NEmpty R.Dom]
  -- : ∀ (a : α), [R.InDom a] → a ∈ R.M ∨ (∃ (max : α), R.InDom max ∧ max ∈ R.M ∧ R max a) := by
  --   intro a aInDom
  --   if h : a ∈ R.M then
  --     exact Or.inl h
  --   else
  --     apply Or.inr
  --     let ⟨cex, cexInDom, h_cex⟩ :=
  --       Rel.not_max_iff_cex.mp h
  --     if h : cex ∈ R.M then
  --       exact ⟨cex, cexInDom, h, h_cex.left⟩
  --     else
        
  --       let ih :=
  --         R.tmp cex
  --       simp [h] at ih
  --       let ⟨max, maxInDom, h_M_max, h_max⟩ := ih 
  --       exists max
  --       apply And.intro maxInDom
  --       apply And.intro h_M_max
  --       apply R.trans h_max h_cex.left

  -- theorem Rel.lemma_1_e_mp
  --   (R : Rel α)
  --   [R.PreOrder]
  --   [Set.Finite R.Dom]
  --   [Set.NEmpty R.Dom]
  -- : (∀ (x y : α), [R.InDom x] → [R.InDom y] → R.M x → R.M y → R.I x y)
  -- → ∀ (a : α), [R.InDom a] → R.C a ↔ R.M a := by
  --   intro get_I_of_M max maxInDom
  --   apply Iff.intro $ R.max_of_best max
  --   intro h_M_max

  --   simp [Membership.mem, C]
  --   apply And.intro maxInDom
  --   intro a' a'InDom
  --   let h := h_M_max.right a'
  --   simp only [P, Decidable.not_and, Decidable.not_not] at h
  --   cases h <;> try assumption
  --   case inl h =>

  --     sorry

    -- apply Decidable.byContradiction
    -- intro h_not_max_R_a'
    -- let h_not_a'_R_max := h_M_max.right a'
    -- simp only [P, Decidable.not_and, Decidable.not_not] at h_not_a'_R_max
    -- cases h_not_a'_R_max with
    -- | inl h_not_a'_R_max =>
      
    --   sorry
    -- | inr h_max_R_a' =>
    --   sorry

    -- apply Decidable.byContradiction
    -- intro h_not_C_max
    -- let ⟨bCex, bCexInDom, h_bCex⟩ :=
    --   Rel.not_best_iff_cex.mp h_not_C_max
    -- let h_bCex' :=
    --   h_M_max.right bCex
    -- simp only [P, Decidable.not_and] at h_bCex'
    -- cases h_bCex' with
    -- | inr h_bCex' =>
    --   exact h_bCex' h_bCex
    -- | inl h_bCex' =>
    --   if h : bCex ∈ R.M then
    --     let h_max_R_bCex :=
    --       get_I_of_M max bCex h_M_max h
    --       |>.left
    --     exact h_bCex h_max_R_bCex
    --   else if h' : bCex ∈ R.C then
    --     apply R.max_of_best bCex h' |> h
    --   else
    --     let ⟨mCex, mCexInDom, h_mCex⟩ :=
    --       Rel.not_max_iff_cex.mp h
    --     let ⟨bCex', bCexInDom', h_bCex'⟩ :=
    --       Rel.not_best_iff_cex.mp h'
    --     simp only [P] at h_mCex
    --     let h_not_mCex_P_max := h_M_max.right mCex
    --     simp only [P, Decidable.not_and] at h_not_mCex_P_max
    --     cases h_not_mCex_P_max with
    --     | inl h =>
          
    --       sorry
    --     | inr h =>
    --       simp [Decidable.not_not] at h
    --       exact R.trans h h_mCex.left |> h_bCex

    -- rw [not_exists] at h_C_empty
    -- let h :=
    --   (h_C_empty max |> not_and.mp)
    --     maxInDom
    -- simp at h
    -- let h := h maxInDom
    -- simp [Decidable.not_forall] at h
    -- sorry

    -- simp
    -- simp [Membership.mem]
    -- apply And.intro maxInDom
    -- intro a' _
    -- let h := h_M_max.right a'
    -- simp only [Rel.P, Decidable.not_and_iff_or_not] at h
    -- cases h
    -- case inl h_not_a'_R_a =>
    --   apply Decidable.byContradiction
    --   sorry
    -- case inr h_a_R_a' =>
    --   apply Decidable.byContradiction
    --   intro h
    --   exact h_a_R_a' h
end lemma_1_e
