import Choice.Chapter1.Section2



/-! # Section 1.3 -/
namespace Choice



/-! ### Lemma `1*a` -/
namespace lemma_1_a
  variable
    [R : Preorder α]
    {x y z : α}

  theorem trans_I : x ≈ y → y ≈ z → x ≈ z :=
    Trans.trans

  theorem trans_PI : x < y → y ≈ z → x < z :=
    fun xy yz => by
      simp [R.lt_def, R.equiv_def] at *
      apply And.intro (Trans.trans xy.left yz.left)
      intro zx
      exact xy.right (Trans.trans yz.left zx)

  theorem trans_IP : x ≈ y → y < z → x < z :=
    fun xy yz => by
      simp [R.lt_def, R.equiv_def] at *
      apply And.intro (Trans.trans xy.left yz.left)
      intro zx
      exact yz.right (Trans.trans zx xy.left)
  
  theorem trans_P : x < y → y < z → x < z :=
    Trans.trans
end lemma_1_a



/-! ### Lemma `1*b` -/
section lemma_1_b
  /- Lemma 1.b.
  
  Original formulation omits the necessary assumption `Inhabited α`. -/
  theorem lemma_1_b
    (α : Type u)
    [R : Preorder α]
    [_F : Finite α]
    [_I : Inhabited α]
  : ∃ max, max ∈ R.M :=
    ⟨R.getMax, R.getMax_in_M rfl⟩

  abbrev Preorder.lemma_1_b
    [Preorder α]
    [Finite α]
    [Inhabited α]
  := Choice.lemma_1_b α
end lemma_1_b



section lemma_1_c
  theorem lemma_1_c'
    [R : Preorder α]
    [_F : Finite α]
    {a b : α}
    (h_ne : a ≠ b)
    (h_only : ∀ (x : α), x = a ∨ x = b)
  : a < b ↔ (∀ c, c ∈ R.C ↔ c = a) := ⟨
    by
      intro a_lt_b c
      constructor
      · intro C_c
        let h := h_only c
        cases h with
        | inl h =>
          assumption
        | inr h =>
          rw [← h] at a_lt_b
          let tmp := C_c a
          simp [R.lt_def] at a_lt_b
          let absurd := a_lt_b.right tmp
          contradiction
      · intro h
        rw [h]
        intro d
        cases h_only d with
        | inl h =>
          rw [h]
        | inr h =>
          rw [h]
          simp [R.lt_def] at a_lt_b
          exact a_lt_b.left
    ,
    by
      intro h
      simp [R.lt_def]
      apply And.intro
      · exact h a |>.mpr rfl b
      · intro b_le_a
        let C_b : b ∈ R.C := by
          intro c
          cases h_only c with
          | inl h =>
            rw [h]
            exact b_le_a
          | inr h =>
            rw [h]
        apply h_ne
        apply Eq.symm
        apply h b |>.mp C_b
  ⟩

  /-- Lemma 1.c.

  Assumption `h_ne` is not in the book, but it is necessary for the theorem's `Iff.mpr`, since `R.P`
  is not reflexive. The book version uses `[x, y]` for the set composed of `x` and `y`, which maybe
  indicates that `x` and `y` should be different 🤷‍♀️. -/
  theorem lemma_1_c
    [R : Preorder α]
    [_F : Finite α]
    {a b : α}
    (h_ne : a ≠ b)
    (h_only : ∀ (x : α), x = a ∨ x = b)
  : a < b ↔ R.C = {a} := by
    constructor
    · intro h
      apply Set.ext
      simp [Set.mem_singleton_of_eq]
      apply (lemma_1_c' h_ne h_only).mp h
    · intro h
      apply (lemma_1_c' h_ne h_only).mpr
      simp [h]
end lemma_1_c



section lemma_1_d
  /-- Lemma 1.d. -/
  theorem lemma_1_d
    [R : Preorder α]
    {best : α}
    (C_best : best ∈ R.C)
  : R.C = R.M :=
    Set.eq_of_subset_of_subset R.best_is_max (
      by
        intro max M_max a
        let best_le_a := C_best a
        let best_le_max := C_best max
        simp [R.M_def] at M_max
        let tmp := M_max best
        simp [R.lt_def] at tmp
        let max_le_best := tmp best_le_max
        apply Trans.trans max_le_best best_le_a
    )
end lemma_1_d



section lemma_1_e

  theorem lemma_1_e_mp
    [R : Preorder α]
    [F : Finite α]
    [I : Inhabited α]
  : (∀ (a b : α), a ∈ R.M → b ∈ R.M → a ≈ b) → (R.C = R.M) := by
    intro h
    let ⟨max, M_max⟩ := R.lemma_1_b
    apply lemma_1_d (best := max)
    apply Decidable.byContradiction
    intro not_C_max
    let ⟨cex, not_max_lt_cex⟩ := R.bestCex not_C_max
    let cex_lt_max : cex < max := by
      simp [R.lt_def]
      apply And.intro _ not_max_lt_cex
      simp [R.M_def] at M_max
      let tmp := M_max cex
      simp only [R.lt_def, not_and_or, not_not] at tmp
      cases tmp with
      | inl h =>
        
        sorry
      | inr h =>
        sorry
    sorry

  theorem lemma_1_e_mpr
    [R : Preorder α]
    [_F : Finite α]
    [_I : Inhabited α]
  : (R.C = R.M) → (∀ (a b : α), a ∈ R.M → b ∈ R.M → a ≈ b) := by
    intro h a b M_a M_b
    let C_a : a ∈ R.C := by rw [h] ; assumption
    let C_b : b ∈ R.C := by rw [h] ; assumption
    simp [R.equiv_def]
    apply And.intro (C_a b) (C_b a)


--   variable
--     {α : Type u}

--   /-- Dependent `P`-chain.

--   Input `hd : α` is the head of the chain. The chain itself represents a path from `hd` to (one of)
--   its `R.max`(s). -/
--   inductive Rel.PChainD (R : Rel α) : α → Type u
--   | max : ∀ {a : α}, a ∈ R.M → R.PChainD a
--   | cons : ∀ {a : α} (b : α),
--     [R.InDom a] → [R.InDom b] → R.P b a → R.PChainD b → R.PChainD a

--   /-- Encodes that `x` appears in a `PChain`, based on `List.Mem`.
  
--   Used for encoding and defining `Membership α R.PChain`. -/
--   inductive Rel.PChainD.Mem
--     {R : Rel α}
--     (x : α)
--   : {hd : α} → R.PChainD hd → Prop
--   | max (h : x ∈ R.M) : Mem x (PChainD.max h)
--   | head [R.InDom x] (b : α) [R.InDom b] (h : R.P b x) (tail : R.PChainD b)
--     : Mem x (PChainD.cons b h tail)
--   | tail (a b : α) [R.InDom a] [R.InDom b] (h : R.P b a) (tail : R.PChainD b)
--     : Mem x tail → Mem x (PChainD.cons b h tail)

--   instance {R : Rel α} {hd : α} : Membership α (R.PChainD hd) where
--     mem (x : α) := Rel.PChainD.Mem x (hd := hd)


--   /-- Same as `PChainD` but erases the chain's head from the type parameters. -/
--   structure Rel.PChain (R : Rel α) : Type u where
--     hd : α
--     dep : R.PChainD hd

--   /-- Same as `PChainD.Mem` but erases the chain's head from the type parameters.
  
--   Used for encoding and defining `Membership α R.PChain`. -/
--   abbrev Rel.PChain.Mem
--     {R : Rel α}
--     (x : α)
--     (chain : R.PChain)
--   : Prop :=
--     PChainD.Mem x chain.dep

--   instance
--     {R : Rel α}
--   : Membership α R.PChain where
--     mem := Rel.PChain.Mem



--   section
--     variable
--       {α : Type u}
--       {R : Rel α}

--     namespace Rel.PChainD
--       def buildOfList
--         {R : Rel α}
--         [R.PreOrder]
--         [R.Finite]
--         [R.NEmpty]
--         (a : α) [a_in_dom : R.InDom a]
--         (l : List α)
--         (h_distinct_l : l.Nodup)
--         (h_l_subset_listDom : l.Subset R.listDom)
--       : R.PChainD a :=
--         R.decideMax a
--           (fun cex cex_in_dom cex_P_a =>
--             PChainD.build cex
--             |> Rel.PChainD.cons cex cex_P_a)
--           Rel.PChainD.max

--       def build
--         {R : Rel α}
--         [R.PreOrder]
--         [R.Finite]
--         [R.NEmpty]
--         (a : α) [a_in_dom : R.InDom a]
--       : R.PChainD a :=
--         R.decideMax a
--           (fun cex cex_in_dom cex_P_a =>
--             PChainD.build cex
--             |> Rel.PChainD.cons cex cex_P_a)
--           Rel.PChainD.max

--       def len : R.PChainD hd → Nat
--       | max _ => 1
--       | cons _ _ tail => 1 + tail.len

--       def zero_lt_len : (chain : R.PChainD hd) → 0 < chain.len
--       | max _ => Nat.zero_lt_succ _
--       | cons b h tail => by
--         simp [len, ←Nat.succ_eq_one_add]
      
--       def len_ne_zero (chain : R.PChainD hd) : chain.len ≠ 0 :=
--         Nat.not_eq_zero_of_lt chain.zero_lt_len



--       theorem all_in_dom
--         {hd : α}
--         (chain : R.PChainD hd)
--         (elm : α)
--       : elm ∈ chain → R.InDom elm
--       | Mem.max h => h.left
--       | Mem.head _b _h _tail => inferInstance
--       | Mem.tail _hd _b _h tail elm_in_tail =>
--         tail.all_in_dom elm elm_in_tail

--       theorem subset_listDom
--         [R.Finite]
--         (chain : R.PChainD hd)
--       : ∀ (a : α), a ∈ chain → a ∈ R.listDom := fun a a_in_chain =>
--         chain.all_in_dom a a_in_chain
--         |> R.listDomIso.mpr

--       theorem head_in_dom
--         {hd : α}
--       : (chain : R.PChainD hd) → hd ∈ chain
--       | max h => Mem.max h
--       | cons b h tail => Mem.head b h tail

--       def getMax
--         {hd : α}
--       : R.PChainD hd → α
--       | max _h_M_hd => hd
--       | cons _ _ tail =>
--         getMax tail

--       theorem getMax_cons
--         {a b : α} [R.InDom a] [R.InDom b]
--         {h : R.P b a}
--         {tail : R.PChainD b}
--       : (Rel.PChainD.cons b h tail).getMax = tail.getMax :=
--         rfl

--       theorem getMax_is_max
--         {hd : α}
--       : (chain : R.PChainD hd) → chain.getMax ∈ R.M
--       | max h => h
--       | cons _ _ tail => by
--         rw [getMax_cons]
--         exact getMax_is_max tail

--       theorem getMax_in_chain
--         {hd : α}
--       : (chain : R.PChainD hd) → chain.getMax ∈ chain
--       | max h => by
--         exact Mem.max h
--       | cons b h_b_P_a tail => by
--         rw [getMax_cons]
--         apply Mem.tail
--         exact getMax_in_chain tail
      
--       theorem getMax_InDom
--         {hd : α}
--       : (chain : R.PChainD hd) → R.InDom chain.getMax :=
--         fun chain =>
--           chain.getMax_is_max.left

--       theorem getMax_R_all
--         [R.PreOrder]
--         {hd : α}
--         (chain : R.PChainD hd)
--       : ∀ (elm : α), elm ∈ chain → R chain.getMax elm := by
--         -- needed for typeclass resolution in the `head` case
--         let _maxInDom := chain.getMax_InDom
--         intro elm h_elm_in_chain
--         cases h_elm_in_chain with
--         | max h_max =>
--           simp [getMax]
--           let hdInDom := h_max.left
--           exact R.refl
--         | head b h_b_P_hd tail =>
--           apply R.trans b
--           apply tail.getMax_R_all
--           apply tail.head_in_dom
--           apply h_b_P_hd.left
--         | tail a b h tail =>
--           rw [getMax_cons]
--           apply getMax_R_all
--           assumption
      
--       theorem getMax_R_head
--         [R.PreOrder]
--         {hd : α}
--         (chain : R.PChainD hd)
--       : R chain.getMax hd :=
--         chain.getMax_R_all hd chain.head_in_dom

--       theorem not_in_chain
--         [R.PreOrder]
--         {a b : α} [R.InDom a] [R.InDom b]
--         (h_b_P_a : R.P b a)
--         (chain : R.PChainD b)
--       : ¬ a ∈ chain := by
--         intro a_in_cons
--         cases a_in_cons with
--         | max _ =>
--           exact h_b_P_a.right h_b_P_a.left
--         | head _ _ _ =>
--           exact h_b_P_a.right h_b_P_a.left
--         | tail b c h_c_P_b tail =>
--           let h_c_P_a :=
--             R.P.trans b h_c_P_b h_b_P_a
--           apply not_in_chain h_c_P_a tail
--           assumption


      
--       -- theorem len_tail
--       --   [R.PreOrder]
--       --   [R.Finite]
--       --   (a b : α) [R.InDom a] [R.InDom b]
--       --   (h_b_P_a : R.P b a)
--       --   (tail : R.PChainD b)
--       --   (chain : R.PChainD a)
--       -- : chain = cons b h_b_P_a tail → tail.len < R.listDom.length := by
--       --   intro h_chain_def
--       --   let h :=
--       --     tail.not_in_chain h_b_P_a
--       --   let a_in_listDom : a ∈ R.listDom :=
--       --     R.listDomIso.mpr inferInstance

--       --   sorry
      
--       -- theorem iso_listDom_of_max_len_mpr
--       --   [R.Finite]
--       --   (chain : R.PChainD hd)
--       -- : chain.len = R.listDom.length → ∀ (a : α), a ∈ R.listDom → a ∈ chain := by
--       --   intro h_len a a_in_listDom
--       --   sorry



--       -- /-- How do I prove this? `/(-_-)\` -/
--       -- theorem len_le_listDom_len
--       --   [R.Finite]
--       --   (chain : R.PChainD hd)
--       -- : chain.len ≤ R.listDom.length := by
--       --   apply Decidable.byContradiction
--       --   intro h
--       --   simp [Nat.lt_of_not_le] at h
--       --   sorry
--     end Rel.PChainD
--   end



--   theorem Rel.lemma_1_e_mpr
--     (R : Rel α)
--     [R.PreOrder]
--     [R.Finite]
--   : (∀ (a : α), [R.InDom a] → R.C a ↔ R.M a)
--   → (x y : α) → [R.InDom x] → [R.InDom y]
--   → R.M x → R.M y
--   → R.I x y := fun h_C_eq_M x y _ _ h_Max_x h_Max_y =>
--     let h_C_x :=
--       (h_C_eq_M x).mpr h_Max_x
--     let h_C_y :=
--       (h_C_eq_M y).mpr h_Max_y
--     ⟨h_C_x.right y, h_C_y.right x⟩


--   -- /-- This is true on finite domains but writing the proof is hard for me. -/
--   -- theorem Rel.tmp
--   --   (R : Rel α)
--   --   [R.PreOrder]
--   --   [R.Finite]
--   --   [R.NEmpty]
--   -- : ∀ (a : α), [R.InDom a] → a ∈ R.M ∨ (∃ (max : α), R.InDom max ∧ max ∈ R.M ∧ R max a) := by
--   --   intro a aInDom
--   --   if h : a ∈ R.M then
--   --     exact Or.inl h
--   --   else
--   --     apply Or.inr
--   --     let ⟨cex, cexInDom, h_cex⟩ :=
--   --       Rel.not_max_iff_cex.mp h
--   --     if h : cex ∈ R.M then
--   --       exact ⟨cex, cexInDom, h, h_cex.left⟩
--   --     else
        
--   --       let ih :=
--   --         R.tmp cex
--   --       simp [h] at ih
--   --       let ⟨max, maxInDom, h_M_max, h_max⟩ := ih 
--   --       exists max
--   --       apply And.intro maxInDom
--   --       apply And.intro h_M_max
--   --       apply R.trans h_max h_cex.left

--   -- theorem Rel.lemma_1_e_mp
--   --   (R : Rel α)
--   --   [R.PreOrder]
--   --   [R.Finite]
--   --   [R.NEmpty]
--   -- : (∀ (x y : α), [R.InDom x] → [R.InDom y] → R.M x → R.M y → R.I x y)
--   -- → ∀ (a : α), [R.InDom a] → R.C a ↔ R.M a := by
--   --   intro get_I_of_M max maxInDom
--   --   apply Iff.intro $ R.max_of_best max
--   --   intro h_M_max

--   --   simp [Membership.mem, C]
--   --   apply And.intro maxInDom
--   --   intro a' a'InDom
--   --   let h := h_M_max.right a'
--   --   simp only [P, Decidable.not_and, Decidable.not_not] at h
--   --   cases h <;> try assumption
--   --   case inl h =>

--   --     sorry

--     -- apply Decidable.byContradiction
--     -- intro h_not_max_R_a'
--     -- let h_not_a'_R_max := h_M_max.right a'
--     -- simp only [P, Decidable.not_and, Decidable.not_not] at h_not_a'_R_max
--     -- cases h_not_a'_R_max with
--     -- | inl h_not_a'_R_max =>
      
--     --   sorry
--     -- | inr h_max_R_a' =>
--     --   sorry

--     -- apply Decidable.byContradiction
--     -- intro h_not_C_max
--     -- let ⟨bCex, bCexInDom, h_bCex⟩ :=
--     --   Rel.not_best_iff_cex.mp h_not_C_max
--     -- let h_bCex' :=
--     --   h_M_max.right bCex
--     -- simp only [P, Decidable.not_and] at h_bCex'
--     -- cases h_bCex' with
--     -- | inr h_bCex' =>
--     --   exact h_bCex' h_bCex
--     -- | inl h_bCex' =>
--     --   if h : bCex ∈ R.M then
--     --     let h_max_R_bCex :=
--     --       get_I_of_M max bCex h_M_max h
--     --       |>.left
--     --     exact h_bCex h_max_R_bCex
--     --   else if h' : bCex ∈ R.C then
--     --     apply R.max_of_best bCex h' |> h
--     --   else
--     --     let ⟨mCex, mCexInDom, h_mCex⟩ :=
--     --       Rel.not_max_iff_cex.mp h
--     --     let ⟨bCex', bCexInDom', h_bCex'⟩ :=
--     --       Rel.not_best_iff_cex.mp h'
--     --     simp only [P] at h_mCex
--     --     let h_not_mCex_P_max := h_M_max.right mCex
--     --     simp only [P, Decidable.not_and] at h_not_mCex_P_max
--     --     cases h_not_mCex_P_max with
--     --     | inl h =>
          
--     --       sorry
--     --     | inr h =>
--     --       simp [Decidable.not_not] at h
--     --       exact R.trans h h_mCex.left |> h_bCex

--     -- rw [not_exists] at h_C_empty
--     -- let h :=
--     --   (h_C_empty max |> not_and.mp)
--     --     maxInDom
--     -- simp at h
--     -- let h := h maxInDom
--     -- simp [Decidable.not_forall] at h
--     -- sorry

--     -- simp
--     -- simp [Membership.mem]
--     -- apply And.intro maxInDom
--     -- intro a' _
--     -- let h := h_M_max.right a'
--     -- simp only [Rel.P, Decidable.not_and_iff_or_not] at h
--     -- cases h
--     -- case inl h_not_a'_R_a =>
--     --   apply Decidable.byContradiction
--     --   sorry
--     -- case inr h_a_R_a' =>
--     --   apply Decidable.byContradiction
--     --   intro h
--     --   exact h_a_R_a' h
end lemma_1_e
