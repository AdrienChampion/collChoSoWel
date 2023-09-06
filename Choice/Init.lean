import Lean.Data.HashMap

import Mathlib.Init.Algebra.Order
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Semiring



theorem Eq.not_symm : ¬ a = b ↔ ¬ b = a := by
  constructor
  <;> (
    intro h h'
    apply h
    rw [h']
  )

theorem Not.ne_symm (ne : Not (a = b)) : ¬ b = a := by
  intro ba
  apply ne
  rw [ba]
