import Lean.Data.HashMap



/-! # Useful types and helpers -/



section list
  def List.leftMost
    (default : α)
    (max : α → α → α)
  : List α → α
  | [] => default
  | head::tail =>
    tail.leftMost default max
    |> max head
  
  theorem List.leftMost_cons
    {max : α → α → α}
    {head default : α}
    {tail : List α}
  : (head :: tail).leftMost default max
  = max head (tail.leftMost default max) := by
    simp [leftMost]

  theorem List.cons_ne_nil : hd::tl ≠ [] := by
    intro
    contradiction

  -- theorem List.leftMost_max
  --   {max : α → α → α}
  --   {res : α}
  --   {list : List α}
  --   {default : α}
  --   (res_def : res = list.leftMost default max)
  -- : ∀ (a : α), a ∈ list → max res a = res := by
  --   intro a
  --   intro h_aInList
  --   cases h_aInList with
  --   | head tail' =>
  --     simp [leftMost] at res_def
  --     rewrite [res_def], 2
  --     sorry
  --   | tail =>
  --     sorry
end list



namespace Choice



def 𝕂 (val : α) : β → α :=
  fun _ => val



-- section hashset
--   open Lean (HashMap)

--   def HashSet
--     (α : Type u) [BEq α] [Hashable α]
--   : Type u:=
--     HashMap α Unit



--   variable
--     {α : Type u} [BEq α] [Hashable α]
  
--   def HashSet.empty (capa : Nat := 8) : HashSet α :=
--     Lean.mkHashMap capa
  
--   instance : EmptyCollection (HashSet α) where
--     emptyCollection := HashSet.empty



--   variable
--     (val : α)
--     (set : HashSet α)

--   section membership
--     def HashSet.contains : Bool :=
--       HashMap.contains set val
--     abbrev HashSet.mem : Prop :=
--       set.contains val

--     instance : Decidable (set.mem val) :=
--       if h : set.contains val then isTrue h else isFalse h

--     instance : Membership α (HashSet α) where
--       mem := HashSet.mem
--   end membership

--   def HashSet.insert : HashSet α :=
--     HashMap.insert set val ()
  
--   def HashSet.erase : HashSet α :=
--     HashMap.erase set val
  
--   def HashSet.isEmpty : Prop :=
--     HashMap.isEmpty set
  
--   instance : Decidable set.isEmpty :=
--     if h : HashMap.isEmpty set then isTrue h else isFalse h
-- end hashset


section set
  abbrev Set (α : Type u) :=
    α → Prop

  variable
    {α : Type u}
    [DecidableEq α]
    (a : α)
    (set : Set α)



  def Set.mem : Prop :=
    set a

  instance {α : outParam (Type u)} : Membership α (Set α) where
    mem := Set.mem



  class Set.Finite (set : Set α) where
    toList : List α
    iso : ∀ {a : α}, a ∈ toList ↔ a ∈ set

  class Set.NEmpty (set : Set α) where
    default : α
    inSet : default ∈ set


  def Set.empty {α : outParam (Type u)} : Set α :=
    𝕂 False
  
  instance : EmptyCollection (Set α) where
    emptyCollection := Set.empty

  theorem Set.empty_mem_none : ¬ a ∈ empty := by
    simp only [empty, Membership.mem, mem, 𝕂]



  def Set.all : Set α :=
    𝕂 True

  theorem Set.all_mem_all : a ∈ all := by
    simp only [all, Membership.mem, mem, 𝕂]



  def Set.add : Set α := fun elm =>
    if elm = a then True else set elm
  def Set.del : Set α := fun elm =>
    if elm = a then False else set elm



  def Set.union (set set' : Set α) : Set α := fun elm =>
    set elm ∨ set' elm
  def Set.inter (set set' : Set α) : Set α := fun elm =>
    set elm ∧ set' elm



  def Set.subset (set set' : Set α) : Prop :=
    ∀ (a : α), set a → set' a
end set
