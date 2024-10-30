import Lean
import LeanTensors.Shape
import Batteries.Data.Array.Lemmas

-- TODO: Come up with a better tactic script.
macro "len_tac" : tactic => `(tactic|try simp ; try omega)

structure Tensor (shape : Shape) (α : Type) where
  data : Array α
  len : data.size = shape.toNat := by len_tac

namespace Tensor

attribute [simp] Tensor.len

variable {s : Shape} {α : Type}

def get (t : Tensor s α) (i : s) : α := t.data[i.idx]

instance : GetElem (Tensor s α) s α (fun _ _ => True) where
  getElem t i _ := t.get i

instance [Add α] : Add (Tensor s α) where
  add u v := { data := u.data.zip v.data |>.map fun (x,y) => x + y }

instance [Sub α] : Sub (Tensor s α) where
  sub u v := { data := u.data.zip v.data |>.map fun (x,y) => x - y }

instance [Mul α] : Mul (Tensor s α) where
  mul u v := { data := u.data.zip v.data |>.map fun (x,y) => x * y }

instance [Div α] : Div (Tensor s α) where
  div u v := { data := u.data.zip v.data |>.map fun (x,y) => x / y }

instance [Neg α] : Neg (Tensor s α) where
  neg u := { data := u.data.map fun x => -x }

instance [Zero α] : Zero (Tensor s α) where
  zero := { data := Array.mkArray s.toNat 0 }

def ofFn {s : Shape} (idx : s → α) : Tensor s α where
  data := Array.ofFn fun i => idx i.asShape

def matmul [Add α] [Mul α] [Zero α] {a b c : Shape} (U : Tensor (a * b) α) (V : Tensor (b * c) α) : 
    Tensor (a * c) α := 
  .ofFn fun (x,y) => Id.run do 
    let mut out : α := 0
    for h : i in [:b.toNat] do
      let z : b := Fin.asShape ⟨i, h.right⟩
      out := out + U.get (x,z) * V.get (z,y)
    return out
  
def concat {a b : Shape} (U : Tensor a α) (V : Tensor b α) : Tensor (a + b) α :=
  .ofFn fun 
    | .inl i => U.get i
    | .inr i => V.get i

def fst {a b : Shape} (U : Tensor (a + b) α) : Tensor a α :=
  .ofFn fun i => U.get (Sum.inl i)

def snd {a b : Shape} (U : Tensor (a + b) α) : Tensor b α :=
  .ofFn fun i => U.get (Sum.inr i)

def lslice {a b : Shape} (U : Tensor (a * b) α) (i : a) : Tensor b α := 
  .ofFn fun y => U.get (i, y)

def rslice {a b : Shape} (U : Tensor (a * b) α) (i : b) : Tensor a α := 
  .ofFn fun x => U.get (x, i)

def uncurry {a b : Shape} (Us : Tensor a (Tensor b α)) : Tensor (a * b) α := 
  .ofFn fun (x,y) => (Us.get x).get y

def curry {a b : Shape} (U : Tensor (a * b) α) : Tensor a (Tensor b α) := 
  .ofFn fun x => .ofFn fun y => U.get (x,y)

def empty : Tensor 0 α where
  data := #[]

def singleton (a : α) : Tensor 1 α where
  data := #[a]

def lunsqueeze {a : Shape} (U : Tensor a α) : Tensor (1 * a) α := 
  .ofFn fun (_,y) => U.get y

def runsqueeze {a : Shape} (U : Tensor a α) : Tensor (a * 1) α := 
  .ofFn fun (y, _) => U.get y

def lsqueeze {a : Shape} (U : Tensor (1 * a) α) : Tensor a α := 
  .ofFn fun y => U.get (show Fin 1 from 0, y)

def rsqueeze {a : Shape} (U : Tensor (a * 1) α) : Tensor a α :=
  .ofFn fun y => U.get (y, show Fin 1 from 0)

def rassoc {a b c : Shape} (U : Tensor ((a * b) * c) α) : Tensor (a * (b * c)) α := 
  .ofFn fun (x, y, z) => U.get ((x, y), z)

def lassoc {a b c : Shape} (U : Tensor (a * (b * c)) α) : Tensor ((a * b) * c) α := 
  .ofFn fun ((x, y), z) => U.get (x, y, z)

def ldistrib {a b c : Shape} (U : Tensor (a * (b + c)) α) : Tensor ((a * b) + (a * c)) α := 
  .ofFn fun 
  | .inl (x, y) => U.get (x, Sum.inl y)
  | .inr (x, y) => U.get (x, Sum.inr y) 

def rdistrib {a b c : Shape} (U : Tensor ((a + b) * c) α) : Tensor ((a * c) + (b * c)) α := 
  .ofFn fun 
  | .inl (x, y) => U.get (Sum.inl x, y)
  | .inr (x, y) => U.get (Sum.inr x, y)

def lundistrib {a b c : Shape} (U : Tensor ((a * b) + (a * c)) α) : Tensor (a * (b + c)) α := 
  .ofFn fun (x, y) => match y with
  | .inl z => U.get <| Sum.inl (x, z)
  | .inr z => U.get <| Sum.inr (x, z)

def rundistrib {a b c : Shape} (U : Tensor ((a * c) + (b * c)) α) : Tensor ((a + b) * c) α := 
  .ofFn fun (x, y) => match x with
  | .inl z => U.get <| Sum.inl (z, y)
  | .inr z => U.get <| Sum.inr (z, y)

def reindex {a b : Shape} (U : Tensor a α) (f : b ≃ a) : Tensor b α := 
  .ofFn fun i => U.get (f i)

def reindex! {a b : Shape} (U : Tensor a α) (h : a.toNat = b.toNat := by len_tac) : Tensor b α where
  data := U.data

example (U : Tensor (4 * 5 + 2) Float) : Tensor (5 * 2 + 3 * 4) Float := U.reindex!

end Tensor
