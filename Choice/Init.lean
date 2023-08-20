import Lean.Data.HashMap

import Mathlib.Init.Algebra.Order
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic



-- namespace List
--   def natIdxOf
--     [DecidableEq α]
--     (l : List α) (a : α) (a_in_l : a ∈ l)
--   : Nat :=
--     aux 0 l a_in_l
--   where aux n (l : List α) (a_in_l : a ∈ l) : Nat :=
--     match l with
--     | [] => by contradiction
--     | hd :: tl =>
--       if h : hd = a then
--         n
--       else
--         aux n.succ tl (by cases a_in_l ; contradiction ; assumption)

--   protected theorem natIdxOf
--     [DecidableEq α]
--     {l : List α} {a : α}
-- end List
