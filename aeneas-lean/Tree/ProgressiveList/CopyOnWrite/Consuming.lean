import Tree.ProgressiveList.CopyOnWrite
import Tree.ProgressiveList.CopyOnWrite.FallbackConsuming

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- A returned filled CoW entry changes only the borrowed list index. This
frame result needs neither cloning laws nor structural invariants. -/
theorem ProgressiveList.get_after_cow_writeback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index query : Std.Usize) (replacement : T)
    (hwrites : update_map.GetCowWithValueWriteReads mapInst ValueInst.corecloneCloneInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    ProgressiveList.get ValueInst mapInst (back (some changed)) query =
      if query = index then ok (some replacement) else ProgressiveList.get ValueInst mapInst self query :=
  ProgressiveList.get_after_cow_writeback_of_fallback
    ValueInst mapInst self index query replacement
    (fun fallback _ => hwrites fallback) hcow hwritten

/-- A filled CoW entry preserves logical length when the relevant maximum
outcomes agree. No exact insertion maximum or separate index bound is needed. -/
theorem ProgressiveList.len_after_cow_writeback {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index length : Std.Usize) (replacement : T)
    (hlen : ProgressiveList.len ValueInst mapInst self = ok length)
    (hmax : update_map.GetCowWithValueMaxIndexAgrees mapInst ValueInst.corecloneCloneInst
      self.updates index self.length)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    ProgressiveList.len ValueInst mapInst (back (some changed)) = ok length :=
  ProgressiveList.len_after_cow_writeback_of_fallback
    ValueInst mapInst self index length replacement hlen
    (fun fallback _ => hmax fallback) hcow hwritten

/-- Returning a filled CoW entry replaces exactly one represented element
and preserves logical length. The input bound is the only sequence premise
beyond representation, and no element-clone identity is needed. -/
theorem ProgressiveList.cow_writeback_represents_set {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize) (replacement : T)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    (hwrites : update_map.GetCowWithValueWriteReads mapInst ValueInst.corecloneCloneInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    (hmax : update_map.GetCowWithValueMaxIndexAgrees mapInst ValueInst.corecloneCloneInst
      self.updates index self.length)
    {handle changed : cow.Cow T} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, back))
    (hwritten : handle.Written replacement changed) :
    (back (some changed)).Represents ValueInst mapInst (contents.set index.val replacement) :=
  ProgressiveList.cow_writeback_represents_set_of_fallback
    ValueInst mapInst self contents index replacement hrep hindex
    (fun fallback _ => hwrites fallback) (fun fallback _ => hmax fallback) hcow hwritten

/-- Accessing and consuming any in-bounds CoW handle succeeds, and writing
through the returned reference replaces precisely that element. All handle,
clone, entry-growth, and metadata continuations are composed from actual
calls. Cloning is required only when no pending value already exists; its
result need not equal the old element. Maximum metadata needs only matching
logical extent, and write-back reads need only agreement after the actual
backing fallback. No backing or packing invariant is needed beyond the original
list representation. -/
theorem ProgressiveList.get_cow_into_mut_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    (hreads : update_map.GetCowWithValueReads mapInst ValueInst.corecloneCloneInst self.updates index)
    (hentry : update_map.GetCowWithValueEntryAt mapInst ValueInst.corecloneCloneInst self.updates index)
    (hexisting : update_map.GetCowWithValueExistingMutable mapInst ValueInst.corecloneCloneInst self.updates index)
    (hwrites : update_map.GetCowWithValueWriteReads mapInst ValueInst.corecloneCloneInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    (hmax : update_map.GetCowWithValueMaxIndexAgrees mapInst ValueInst.corecloneCloneInst
      self.updates index self.length)
    (hclone : mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone contents[index.val] = ok value) :
    ∃ handle listBack value valueBack,
      ProgressiveList.get_cow ValueInst mapInst self index = ok (some handle, listBack) ∧
      cow.Cow.into_mut ValueInst.corecloneCloneInst handle = ok (.Ok value, valueBack) ∧
      handle.value = contents[index.val] ∧ handle.MaterializedValue ValueInst.corecloneCloneInst value ∧
      ∀ replacement,
        (listBack (some (valueBack (.Ok replacement)))).Represents ValueInst mapInst (contents.set index.val replacement) ∧
        (listBack (some (valueBack (.Ok replacement)))).tree = self.tree ∧
        (listBack (some (valueBack (.Ok replacement)))).length = self.length :=
  ProgressiveList.get_cow_into_mut_spec_of_fallback
    ValueInst mapInst self contents index hrep hindex
    (fun fallback _ => hreads fallback) (fun fallback _ => hentry fallback)
    (fun fallback _ => hexisting fallback) (fun fallback _ => hwrites fallback)
    (fun fallback _ => hmax fallback) hclone

end milhouse.progressive_list
