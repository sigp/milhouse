import Tree.Cow.Value

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- The handle carries an existing pending value, or the supplied fallback
    when no pending value exists. This generic map law includes failure
    behavior and does not require cloning merely to obtain a handle. -/
def GetCowWithValueReads {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback,
    (do let (handle, _) ← mapInst.get_cow_with_value cloneInst updates index fallback
        ok (handle.map cow.Cow.value)) =
      (do let pending ← mapInst.get updates index
          ok (pending.or fallback))

/-- Releasing the returned handle unchanged preserves the complete update
    map, including metadata and the absence of a materialized fallback. The
    same law covers a missing handle. -/
def GetCowWithValuePreserves {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (handle, back) →
      back handle = updates

end milhouse.update_map
