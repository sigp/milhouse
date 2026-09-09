import Tree.Cow.Consuming
import Tree.UpdateMap.Length.Equivalence

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

/-- A filled CoW footprint preserves maximum-query outcomes relevant to the
given backing length. The map need not expose the exact insertion maximum;
the separate write law still specifies the replacement and lookup frame. -/
def GetCowWithValueMaxIndexAgrees {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (previous : utils.Length) : Prop :=
  ∀ fallback handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
    ∀ replacement changed, handle.Written replacement changed →
    utils.MaxIndexResultsAgree previous
      (mapInst.max_index (back (some changed))) (mapInst.max_index updates)

/-- Exact insertion metadata suffices for observer agreement whenever the
borrowed key is below an existing successful logical length. -/
theorem GetCowWithValueMaxIndex.agrees_of_in_bounds {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (previous : utils.Length) (length : Std.Usize)
    (hmax : GetCowWithValueMaxIndex mapInst cloneInst updates index)
    (hlen : utils.updated_length mapInst previous updates = ok length)
    (hindex : index.val < length.val) :
    GetCowWithValueMaxIndexAgrees mapInst cloneInst updates index previous := by
  intro fallback handle back hcall replacement changed hwritten
  exact utils.max_index_results_agree_of_insert_below mapInst previous updates
    (back (some changed)) index length hlen hindex
    (hmax fallback handle back hcall replacement changed hwritten)

end milhouse.update_map
