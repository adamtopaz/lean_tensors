This repository contains some experiments in setting up tensors in Lean4.
The shapes allowed are *different* from the usual approach of lists of naturals.
Instead, we introduce a type of shapes as follows;

```lean
inductive Shape where 
  | of : Nat -> Shape
  | add : Shape -> Shape -> Shape
  | mul : Shape -> Shape -> Shape
```

and to each `s : Shape` we associate a carrier type:
```lean
def Shape.Carrier : Shape → Type
  | .of n => Fin n
  | .add s₁ s₂ => s₁.Carrier ⊕ s₂.Carrier 
  | .mul s₁ s₂ => s₁.Carrier × s₂.Carrier
```

This function is registered as a coercion to sort, so one can consider `s : Shape` as a type.
When `U : Tensor s Float` is a tensor of shape `s : S` and `i : s`, `U.get i` is the value of the tensor at position `i`.

The type `Tensor s α` is defined as
```lean
structure Tensor (s : Shape) (α : Type) where
  data : Array α
  len : data.size = s.toNat
```
The expression associated to `s` is what governs the retrieval of the data from the array.

