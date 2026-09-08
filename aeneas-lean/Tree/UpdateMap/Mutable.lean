import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- The read law for a mutable map lookup: an existing entry takes precedence;
    otherwise the fallback is evaluated at the requested key. This law concerns
    the generic map primitive, independently of any list or backing tree. -/
def GetMutWithReads {T U : Type} (mapInst : UpdateMap U T)
    (updates : U) (index : Std.Usize) : Prop :=
  ∀ {F : Type} (fnInst : core.ops.function.FnOnce F Std.Usize (Option T)) (fallback : F),
    (do
      let (value, _) ← mapInst.get_mut_with fnInst updates index fallback
      ok value) = (do
      let pending ← mapInst.get updates index
      match pending with
      | some value => ok (some value)
      | none => fnInst.call_once fallback index)

/-- Writing through a present mutable handle changes only its key. The
    replacement is `some`: changing the shape of the returned `Option<&mut T>`
    is not a Rust write through the borrowed element. -/
def GetMutWithWrites {T U : Type} (mapInst : UpdateMap U T)
    (updates : U) (index : Std.Usize) : Prop :=
  ∀ {F : Type} (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (fallback : F) (value : T) (back : Option T → U),
    mapInst.get_mut_with fnInst updates index fallback = ok (some value, back) →
    ∀ replacement query, mapInst.get (back (some replacement)) query =
      if query = index then ok (some replacement) else mapInst.get updates query

end milhouse.update_map
