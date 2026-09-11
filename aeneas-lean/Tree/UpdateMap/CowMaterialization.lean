import Tree.Cow.Consuming

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- Structural entry readiness and clone termination for the handles from
one actual supplied-fallback invocation. Cloning is required only for an
immutable handle; no clone identity, entry-key equality, or mutation success
is assumed. -/
def GetCowWithValueMaterializationInputsFor {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (fallback : Option T) : Prop :=
  ∀ handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
      handle.CanMaterialize ∧
        (handle.NeedsClone = true → ∃ value, cloneInst.clone handle.value = ok value)

end milhouse.update_map
