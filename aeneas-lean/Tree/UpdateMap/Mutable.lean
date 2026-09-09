import Tree.UpdateMap.Length.Equivalence

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

/-- Mutable access records the borrowed key in maximum-index metadata. This
    also covers materializing a previously absent entry from the fallback. -/
def GetMutWithMaxIndex {T U : Type} (mapInst : UpdateMap U T)
    (updates : U) (index : Std.Usize) : Prop :=
  ∀ {F : Type} (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (fallback : F) (value : T) (back : Option T → U),
    mapInst.get_mut_with fnInst updates index fallback = ok (some value, back) →
    ∀ replacement oldMax, mapInst.max_index updates = ok oldMax →
      mapInst.max_index (back (some replacement)) = ok (some (oldMax.elim index
        (core.cmp.impls.OrdUsize.max index)))

/-- Mutable write-back preserves the extent described by maximum metadata at
the given backing length. This constrains raw query outcomes, including
failure and divergence, without prescribing an exact insertion maximum. -/
def GetMutWithMaxIndexAgrees {T U : Type} (mapInst : UpdateMap U T)
    (updates : U) (index : Std.Usize) (previous : utils.Length) : Prop :=
  ∀ {F : Type} (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (fallback : F) (value : T) (back : Option T → U),
    mapInst.get_mut_with fnInst updates index fallback = ok (some value, back) →
    ∀ replacement, utils.MaxIndexResultsAgree previous
      (mapInst.max_index (back (some replacement))) (mapInst.max_index updates)

/-- The usual exact insertion contract supplies the weaker observer contract
for every write below an existing successful logical length. -/
theorem GetMutWithMaxIndex.agrees_of_in_bounds {T U : Type} (mapInst : UpdateMap U T)
    (updates : U) (index : Std.Usize) (previous : utils.Length) (length : Std.Usize)
    (hmax : GetMutWithMaxIndex mapInst updates index)
    (hlen : utils.updated_length mapInst previous updates = ok length)
    (hindex : index.val < length.val) :
    GetMutWithMaxIndexAgrees mapInst updates index previous := by
  intro F fnInst fallback value back hcall replacement
  exact utils.max_index_results_agree_of_insert_below mapInst previous updates
    (back (some replacement)) index length hlen hindex
    (hmax fnInst fallback value back hcall replacement)

/-- A missing mutable lookup leaves the map unchanged when its absent handle
    is released. No element reference exists through which to write a value. -/
def GetMutWithMissing {T U : Type} (mapInst : UpdateMap U T)
    (updates : U) (index : Std.Usize) : Prop :=
  ∀ {F : Type} (fnInst : core.ops.function.FnOnce F Std.Usize (Option T))
    (fallback : F) (back : Option T → U),
    mapInst.get_mut_with fnInst updates index fallback = ok (none, back) →
      back none = updates

end milhouse.update_map
