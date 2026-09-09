import Tree.Cow.Consuming

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- A present CoW loan contains the requested vacant entry, or an already
mutable value. This is an entry-location law, not a mutation-success premise. -/
def GetCowWithValueEntryAt {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
      handle.EntryAt index

/-- Existing pending values are already borrowed mutably; consuming that
handle does not clone an element. -/
def GetCowWithValueExistingMutable {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
    ∀ value, mapInst.get updates index = ok (some value) → handle.NeedsClone = false

/-- Returning a filled entry footprint stores the replacement at its key and
frames all other lookups. `Written` describes data/metadata effects only;
the actual consuming method is proved separately to produce that footprint. -/
def GetCowWithValueWrites {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
    ∀ replacement changed, handle.Written replacement changed →
    ∀ query, mapInst.get (back (some changed)) query =
      if query = index then ok (some replacement) else mapInst.get updates query

/-- The map interprets a returned filled slot and recorded callback as an
insertion at the borrowed key, including first materialization of a fallback. -/
def GetCowWithValueMaxIndex {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
    ∀ replacement changed, handle.Written replacement changed →
    ∀ oldMax, mapInst.max_index updates = ok oldMax →
      mapInst.max_index (back (some changed)) = ok (some (oldMax.elim index
        (core.cmp.impls.OrdUsize.max index)))

end milhouse.update_map
