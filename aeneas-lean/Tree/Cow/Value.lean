import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.cow

/-- The element carried by the extracted handle's data. This observation is
    independent of a call to Rust `Deref`, whose extraction bridge is pending. -/
def Cow.value {T : Type} : Cow T → T
  | .BTree (.Immutable value _) _ => value
  | .BTree (.Mutable value) _ => value
  | .Vec (.Immutable value _) _ => value
  | .Vec (.Mutable value) _ => value

/-- The optional action that records a map index upon materialization. -/
def Cow.onMut {T : Type} : Cow T → CowOnMut
  | .BTree _ onMut => onMut
  | .Vec _ onMut => onMut

end milhouse.cow
