import Choice.Init



/-! # Section 1.1 -/
namespace Choice


/-- A relation over some domain. -/
structure Rel (α : Type u) where
  /-- The relation's domain. -/
  Dom : Set α
  /-- The actual relation. -/
  R : α → α → Prop
  /-- `R` is decidable. -/
  decidable {a a' : α} : Decidable (R a a')



instance : CoeFun (Rel α) (fun _ => α → α → Prop) where
  coe rel := rel.R

instance : CoeSort (Rel α) (α → α → Prop) where
  coe rel := rel.R

instance {R : Rel α} : Decidable (R a a') :=
  R.decidable

instance : Membership α (Rel α) where
  mem a rel := a ∈ rel.Dom



def Rel.listDom (R : Rel α) [I : Set.Finite R.Dom] : List α :=
  I.toList

def Rel.default (R : Rel α) [I : Set.NEmpty R.Dom] : α :=
  I.default

def Rel.nemptyListDom
  (R : Rel α)
  [instFinite : Set.Finite R.Dom]
  [instNEmpty : Set.NEmpty R.Dom]
: R.listDom ≠ [] := by
  let h_nempty : R.default ∈ R.listDom :=
    instFinite.iso.mpr instNEmpty.inSet
  intro h_empty
  rw [h_empty] at h_nempty
  contradiction



/-- Encodes that `a ∈ R.Dom`.

Having this typeclass avoids passing `a ∈ R.Dom` everywhere, and lets us mostly forget about it. -/
class Rel.InDom (R : Rel α) (a : α) where
  inDom : a ∈ R

instance
  {R : Rel α}
  [I : Set.NEmpty R.Dom]
: R.InDom R.default where
  inDom := I.inSet

def Rel.inListToInDom
  {R : Rel α}
  [I : Set.Finite R.Dom]
  {a : α}
  (h : a ∈ I.toList)
: R.InDom a where
  inDom := I.iso.mp h

def Rel.liftListProp
  (R : Rel α)
  [I : Set.Finite R.Dom]
  {P : α → Prop}
: (∀ (a : α), a ∈ I.toList → P a) → ∀ (a : α), [R.InDom a] → P a :=
  fun h a aInDom =>
    h a $ I.iso.mpr aInDom.inDom



section
  variable
    {α : Type u}
    (R : Rel α)

  /-! ### Basic relation properties -/
  section basic
    class Rel.Refl where
      refl [InDom R a] : R a a

    class Rel.Total where
      total [InDom R a] :
        a ≠ a' → (R a a' ∨ R a' a)

    class Rel.Trans where
      trans [InDom R a] :
        R a a' → R a' a'' → R a a''

    class Rel.AntiSym where
      antiSym [InDom R a] :
        R a a' → R a' a → a = a'

    class Rel.Asym where
      asym [InDom R a] :
        R a a' → ¬ R a' a

    class Rel.Sym where
      sym [InDom R a] :
        R a a' → R a' a
  end basic



  /-! ### Composite properties over relations -/
  section comp
    /-- Reflexive and transitive, called *quasi-order* in the book. -/
    class Rel.PreOrder
      extends Refl R, Trans R

    instance [R.Refl] [R.Trans] : R.PreOrder where
      toRefl := inferInstance
      toTrans := inferInstance



    /-- Total pre-order. -/
    class Rel.Order
      extends R.PreOrder, R.Total

    instance [R.PreOrder] [R.Total] : R.Order where
      toPreOrder := inferInstance
      toTotal := inferInstance



    /-- Anti-symmetric pre-order. -/
    class Rel.PartialOrder
      extends R.PreOrder, R.AntiSym

    instance [R.PreOrder] [R.AntiSym] : R.PartialOrder where
      toPreOrder := inferInstance
      toAntiSym := inferInstance



    /-- Anti-symmetric (total) order. -/
    class Rel.Chain
      extends R.Order, R.AntiSym
    
    instance
      [Io : R.Order]
      [Ipo : R.PartialOrder]
    : R.Chain where
      toOrder := Io
      toAntiSym := Ipo.toAntiSym

    instance
      [I : R.Chain]
    : R.PartialOrder where
      toPreOrder := I.toPreOrder
      toAntiSym := I.toAntiSym



    /-- Transitive and asymmetric. -/
    class Rel.StrictPartialOrder
      extends R.Trans, R.Asym

    instance [R.Trans] [R.Asym] : R.StrictPartialOrder where
      toTrans := inferInstance
      toAsym := inferInstance



    /-- Total strict-partial-order. -/
    class Rel.StrongOrder
      extends R.StrictPartialOrder, R.Total

    instance [R.StrictPartialOrder] [R.Total] : R.StrongOrder where
      toStrictPartialOrder := inferInstance
      toTotal := inferInstance
  end comp
end