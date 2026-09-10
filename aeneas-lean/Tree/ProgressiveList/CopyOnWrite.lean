import Tree.ProgressiveList.CopyOnWrite.Conditions

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The element carried by the returned handle agrees with `get`, including
    missing indices and failures. Neither lookup clones the element, so no
    element-cloning law is imposed. -/
theorem ProgressiveList.get_cow_read_eq_get {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index) :
    (do let (handle, _) ← ProgressiveList.get_cow ValueInst mapInst self index
        ok (handle.map cow.Cow.value)) = ProgressiveList.get ValueInst mapInst self index :=
  ProgressiveList.get_cow_read_eq_get_of_fallback
    ValueInst mapInst self index (fun fallback _ => hreads fallback)

/-- Successful copy-on-write access carries the value of the corresponding
    immutable read. This observes the handle's data; the Rust `Deref` bridge
    is a separate extraction obligation. -/
theorem ProgressiveList.get_cow_reads_get {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ProgressiveList.get ValueInst mapInst self index = ok (handle.map cow.Cow.value) :=
  ProgressiveList.get_cow_reads_get_of_fallback
    ValueInst mapInst self index (fun fallback _ => hreads fallback) hcow

/-- If immutable lookup succeeds, copy-on-write access succeeds and carries
    the same optional value. No cloning or structural invariant is required. -/
theorem ProgressiveList.get_cow_succeeds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    {value : Option T}
    (hget : ProgressiveList.get ValueInst mapInst self index = ok value) :
    ∃ handle back,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back) ∧
      handle.map cow.Cow.value = value :=
  ProgressiveList.get_cow_succeeds_of_fallback
    ValueInst mapInst self index (fun fallback _ => hreads fallback) hget

/-- Missing immutable lookup gives a missing copy-on-write handle. -/
theorem ProgressiveList.get_cow_none_of_get_none {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok none) :
    ∃ back, ProgressiveList.get_cow ValueInst mapInst self index = ok (none, back) :=
  ProgressiveList.get_cow_none_of_get_none_of_fallback
    ValueInst mapInst self index (fun fallback _ => hreads fallback) hget

/-- Releasing a returned handle unchanged preserves the entire list, including
    pending values and maximum-index metadata. It does not materialize a
    fallback value. The map's release law suffices without a lookup law. -/
theorem ProgressiveList.get_cow_read_only_preserves_self {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize)
    (hpreserves : update_map.GetCowWithValuePreserves mapInst ValueInst.corecloneCloneInst
      self.updates index)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    back handle = self :=
  ProgressiveList.get_cow_read_only_preserves_self_of_fallback
    ValueInst mapInst self index (fun fallback _ => hpreserves fallback) hcow

/-- **Read-only sequence correctness.** A represented list yields exactly the
    indexed optional element in its handle data, and releasing that handle
    unchanged restores the entire list. Bounds follow from representation;
    no element-cloning law or additional tree invariant is needed. -/
theorem ProgressiveList.get_cow_represents_read {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hpreserves : update_map.GetCowWithValuePreserves mapInst ValueInst.corecloneCloneInst
      self.updates index) :
    ∃ handle back,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back) ∧
      handle.map cow.Cow.value = contents[index.val]? ∧ back handle = self :=
  ProgressiveList.get_cow_represents_read_of_fallback
    ValueInst mapInst self contents index hrep
    (fun fallback _ => hreads fallback) (fun fallback _ => hpreserves fallback)

/-- Out-of-bounds copy-on-write access returns no handle and preserves the
    entire list when released. -/
theorem ProgressiveList.get_cow_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hindex : contents.length ≤ index.val)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hpreserves : update_map.GetCowWithValuePreserves mapInst ValueInst.corecloneCloneInst
      self.updates index) :
    ∃ back, ProgressiveList.get_cow ValueInst mapInst self index = ok (none, back) ∧
      back none = self :=
  ProgressiveList.get_cow_out_of_bounds_of_fallback
    ValueInst mapInst self contents index hrep hindex
    (fun fallback _ => hreads fallback) (fun fallback _ => hpreserves fallback)

end milhouse.progressive_list
