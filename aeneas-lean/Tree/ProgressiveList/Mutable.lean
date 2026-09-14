import Tree.ProgressiveList.Mutable.Fallback

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Mutable access returns an existing pending value directly; otherwise it
returns the actual clone of the backing value. This equation preserves clone
failure and nonidentity results and requires only the generic map read law. -/
theorem ProgressiveList.get_mut_read_eq_pending_or_clone {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetMutWithReads mapInst self.updates index) :
    (do let (value, _) ← ProgressiveList.get_mut ValueInst mapInst self index
        ok value) = (do
      let pending ← mapInst.get self.updates index
      match pending with
      | some value => ok (some value)
      | none => do
        let backing ← ProgressiveList.backing_get ValueInst mapInst self index
        core.option.OptionShared0T.cloned ValueInst.corecloneCloneInst backing) :=
  ProgressiveList.get_mut_read_eq_pending_or_clone_of_fallback
    ValueInst mapInst self index (hreads _ _)

/-- Read agreement with `get` needs identity cloning only for an actual
    backing fallback after a missing pending lookup. Pending values, missing
    backing reads, and failing reads need no cloning premise. -/
theorem ProgressiveList.get_mut_read_eq_get {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hclone : mapInst.get self.updates index = ok none → ∀ value,
      ProgressiveList.backing_get ValueInst mapInst self index = ok (some value) →
      ValueInst.corecloneCloneInst.clone value = ok value) :
    (do let (value, _) ← ProgressiveList.get_mut ValueInst mapInst self index
        ok value) = ProgressiveList.get ValueInst mapInst self index :=
  ProgressiveList.get_mut_read_eq_get_of_fallback
    ValueInst mapInst self index (hreads _ _) hclone

/-- Mutable access reads the same value as `get`, including `none` at missing
    indices, under the map lookup law and value-preserving element cloning. -/
theorem ProgressiveList.get_mut_reads_get {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hclone : mapInst.get self.updates index = ok none → ∀ value,
      ProgressiveList.backing_get ValueInst mapInst self index = ok (some value) →
      ValueInst.corecloneCloneInst.clone value = ok value)
    {value : Option T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back)) :
    ProgressiveList.get ValueInst mapInst self index = ok value :=
  ProgressiveList.get_mut_reads_get_of_fallback
    ValueInst mapInst self index (hreads _ _) hclone hmut

/-- Whenever the corresponding immutable read succeeds, mutable access also
    succeeds with the same optional element and a write-back continuation. -/
theorem ProgressiveList.get_mut_succeeds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hclone : mapInst.get self.updates index = ok none → ∀ value,
      ProgressiveList.backing_get ValueInst mapInst self index = ok (some value) →
      ValueInst.corecloneCloneInst.clone value = ok value)
    {value : Option T}
    (hget : ProgressiveList.get ValueInst mapInst self index = ok value) :
    ∃ back, ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back) :=
  ProgressiveList.get_mut_succeeds_of_fallback
    ValueInst mapInst self index (hreads _ _) hclone hget

/-- A missing immutable lookup is also missing under mutable access. There is
    no element to clone, so this result requires no element-cloning law. -/
theorem ProgressiveList.get_mut_none_of_get_none {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok none) :
    ∃ back, ProgressiveList.get_mut ValueInst mapInst self index = ok (none, back) :=
  ProgressiveList.get_mut_none_of_get_none_of_fallback
    ValueInst mapInst self index (hreads _ _) hget

/-- Writing through a present mutable handle changes only the selected list
    element, including all pending and backing lookups at other indices. -/
theorem ProgressiveList.get_after_get_mut_at {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    (hwrites : update_map.GetMutWithWriteReads mapInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.get ValueInst mapInst (back (some replacement)) query =
      if query = index then ok (some replacement)
      else ProgressiveList.get ValueInst mapInst self query :=
  ProgressiveList.get_after_get_mut_at_of_fallback
    ValueInst mapInst self index query replacement (hwrites _ _) hmut

/-- A mutable write preserves logical length under agreement of the relevant
maximum-query outcomes. Exact insertion metadata and a separate index bound
are unnecessary for this observer result. -/
theorem ProgressiveList.len_after_get_mut {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index length : Std.Usize) (replacement : T)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length)
    (hmax : update_map.GetMutWithMaxIndexAgrees mapInst self.updates index self.length)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    ProgressiveList.len ValueInst mapInst (back (some replacement)) = ok length :=
  ProgressiveList.len_after_get_mut_of_fallback
    ValueInst mapInst self index length replacement hlen (hmax _ _) hmut

/-- **Sequence replacement correctness.** Writing a new value through a
    returned mutable element handle preserves length and every other element.
    The old representation and successful read supply the index bound, so
    callers need no separate bounds or tree invariants. -/
theorem ProgressiveList.get_mut_represents_set {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hwrites : update_map.GetMutWithWriteReads mapInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    (hmax : update_map.GetMutWithMaxIndexAgrees mapInst self.updates index self.length)
    {value : T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back)) :
    (back (some replacement)).Represents ValueInst mapInst
      (contents.set index.val replacement) :=
  ProgressiveList.get_mut_represents_set_of_fallback
    ValueInst mapInst self contents index replacement hrep
    (hreads _ _) (hwrites _ _) (hmax _ _) hmut

/-- Releasing a missing mutable handle preserves the complete list, under the
    generic map's missing-lookup law. -/
theorem ProgressiveList.get_mut_none_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hmissing : update_map.GetMutWithMissing mapInst self.updates index)
    {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (none, back)) :
    back none = self :=
  ProgressiveList.get_mut_none_preserves_self_of_fallback
    ValueInst mapInst self index (hmissing _ _) hmut

/-- Out-of-bounds mutable access successfully returns no element and leaves
    the entire list unchanged. Representation supplies the missing immutable
    read, while map laws supply the corresponding mutable behavior. No element
    cloning law is needed for a missing lookup. -/
theorem ProgressiveList.get_mut_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hindex : contents.length ≤ index.val)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hmissing : update_map.GetMutWithMissing mapInst self.updates index) :
    ∃ back, ProgressiveList.get_mut ValueInst mapInst self index = ok (none, back) ∧
      back none = self :=
  ProgressiveList.get_mut_out_of_bounds_of_fallback
    ValueInst mapInst self contents index hrep hindex (hreads _ _) (hmissing _ _)

end milhouse.progressive_list
