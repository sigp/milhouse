import Tree.Cow.Consuming
import Tree.UpdateMap.Length.Equivalence
import Tree.UpdateMap.Lookup

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.update_map

/-- Entry location for present handles from one supplied fallback value. -/
def GetCowWithValueEntryAtFor {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (fallback : Option T) : Prop :=
  ∀ handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
      handle.EntryAt index

/-- A present CoW loan contains the requested vacant entry, or an already
mutable value. This is an entry-location law, not a mutation-success premise. -/
def GetCowWithValueEntryAt {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback, GetCowWithValueEntryAtFor mapInst cloneInst updates index fallback

/-- Pending-value handles from one supplied fallback need no element clone. -/
def GetCowWithValueExistingMutableFor {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (fallback : Option T) : Prop :=
  ∀ handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
    ∀ value, mapInst.get updates index = ok (some value) → handle.NeedsClone = false

/-- Existing pending values are already borrowed mutably; consuming that
handle does not clone an element. -/
def GetCowWithValueExistingMutable {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize) : Prop :=
  ∀ fallback, GetCowWithValueExistingMutableFor mapInst cloneInst updates index fallback

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

/-- Lookup agreement for filled handles from one supplied fallback value. -/
def GetCowWithValueWriteReadsFor {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (backing : Std.Usize → Result (Option T)) (fallback : Option T) : Prop :=
  ∀ handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
    ∀ replacement changed, handle.Written replacement changed →
    ∀ query, LookupResultsAgree (backing query)
      (mapInst.get (back (some changed)) query)
      (if query = index then ok (some replacement) else mapInst.get updates query)

/-- A filled CoW footprint gives the replacement and frames other reads
after the supplied backing fallback. The actual entry and callback effects
remain described by `Written`; exact pending-map answers are unnecessary. -/
def GetCowWithValueWriteReads {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (backing : Std.Usize → Result (Option T)) : Prop :=
  ∀ fallback, GetCowWithValueWriteReadsFor mapInst cloneInst updates index backing fallback

/-- The exact CoW insertion/lookup law implies agreement after any backing
fallback, retaining the same actual filled-entry footprint. -/
theorem GetCowWithValueWrites.read_agreement {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (backing : Std.Usize → Result (Option T))
    (hwrites : GetCowWithValueWrites mapInst cloneInst updates index) :
    GetCowWithValueWriteReads mapInst cloneInst updates index backing := by
  intro fallback handle back hcall replacement changed hwritten query
  exact LookupResultsAgree.of_eq _
    (hwrites fallback handle back hcall replacement changed hwritten query)

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

/-- Maximum-result agreement for filled handles from one supplied fallback. -/
def GetCowWithValueMaxIndexAgreesFor {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (previous : utils.Length) (fallback : Option T) : Prop :=
  ∀ handle back,
    mapInst.get_cow_with_value cloneInst updates index fallback = ok (some handle, back) →
    ∀ replacement changed, handle.Written replacement changed →
    utils.MaxIndexResultsAgree previous
      (mapInst.max_index (back (some changed))) (mapInst.max_index updates)

/-- A filled CoW footprint preserves maximum-query outcomes relevant to the
given backing length. The map need not expose the exact insertion maximum;
the separate write law still specifies the replacement and lookup frame. -/
def GetCowWithValueMaxIndexAgrees {T U : Type} (mapInst : UpdateMap U T)
    (cloneInst : core.clone.Clone T) (updates : U) (index : Std.Usize)
    (previous : utils.Length) : Prop :=
  ∀ fallback, GetCowWithValueMaxIndexAgreesFor mapInst cloneInst updates index previous fallback

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
