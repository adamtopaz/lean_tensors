import Mathlib.Logic.Equiv.Fin

inductive Shape where 
  | of : Nat -> Shape
  | add : Shape -> Shape -> Shape
  | mul : Shape -> Shape -> Shape

instance : Add Shape := ⟨Shape.add⟩ 
instance : Mul Shape := ⟨Shape.mul⟩
instance (n : Nat) : OfNat Shape n := ⟨Shape.of n⟩
instance : Zero Shape := ⟨Shape.of 0⟩

@[simp]
def Shape.toNat : Shape -> Nat
  | .of n => n
  | .add s₁ s₂ => s₁.toNat + s₂.toNat
  | .mul s₁ s₂ => s₁.toNat * s₂.toNat

def Shape.Carrier : Shape → Type
  | .of n => Fin n
  | .add s₁ s₂ => s₁.Carrier ⊕ s₂.Carrier 
  | .mul s₁ s₂ => s₁.Carrier × s₂.Carrier

instance : CoeSort Shape Type where
  coe := Shape.Carrier

def Shape.equivFin (s : Shape) : s ≃ Fin s.toNat := 
  match s with 
  | .of _ => Equiv.refl _
  | .add a b => Equiv.trans (Equiv.sumCongr a.equivFin b.equivFin) finSumFinEquiv
  | .mul a b => Equiv.trans (Equiv.prodCongr a.equivFin b.equivFin) finProdFinEquiv

abbrev Shape.Carrier.idx (s : Shape) : s → Fin s.toNat := s.equivFin
abbrev Fin.asShape {s : Shape} : Fin s.toNat → s := s.equivFin.symm

