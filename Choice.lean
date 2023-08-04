import Choice.Init
import Choice.Chapter1


-- variable
--   {α : Type u}

-- def dummyMax (_ : α) : Prop :=
--   True

-- inductive Chain.Ex (R : α → α → Prop) : α → Type u
-- | max a : dummyMax a → Chain.Ex R a
-- | rel (a b : α) : R b a → Chain.Ex R b → Chain.Ex R a

-- inductive Chain.Ex.Mem (x : α) : {c : α} → Chain.Ex R c → Prop
-- | max (h : dummyMax x) : Mem x (Chain.Ex.max x h)
-- | head (a b : α) (h : R b a) (tail : Chain.Ex R b)
--   : Mem x tail → Mem x (Chain.Ex.rel a b h tail)

-- structure Chain (R : α → α → Prop) : Type u where
--   hd : α
--   ex : Chain.Ex R hd

-- abbrev Chain.Mem {R : α → α → Prop} (x : α) (chain : Chain R) : Prop :=
--   Chain.Ex.Mem x chain.ex

-- instance
--   {R : α → α → Prop}
-- : Membership α (Chain R) where
--   mem := Chain.Mem
