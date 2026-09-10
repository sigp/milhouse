import Tree.ProgressiveList.Mutable
import Tree.ProgressiveList.Mutable.Conditions

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Mutable access to a present element succeeds if the one possible fallback
clone succeeds. An existing pending value is returned directly; otherwise the
returned value is the actual clone result, which need not equal the old value. -/
theorem ProgressiveList.get_mut_present_succeeds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (old : T)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok (some old))
    (hclone : mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone old = ok value) :
    ∃ value back,
      ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back) ∧
      ((mapInst.get self.updates index = ok (some old) ∧ value = old) ∨
       (mapInst.get self.updates index = ok none ∧
        ValueInst.corecloneCloneInst.clone old = ok value)) :=
  ProgressiveList.get_mut_present_succeeds_of_fallback
    ValueInst mapInst self index old (hreads _ _) hget hclone

/-- Accessing any represented in-bounds element succeeds, and writing through
the returned reference replaces exactly that element while preserving the
backing tree and its recorded length. The initial value is either the pending
element or the actual fallback clone. Only that clone must terminate, and it
need not preserve the old element. Maximum metadata needs only matching
logical extent, and write-back reads need only agreement after the actual
backing fallback. No structural backing invariant is needed. -/
theorem ProgressiveList.get_mut_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : index.val < contents.length)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hwrites : update_map.GetMutWithWriteReads mapInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    (hmax : update_map.GetMutWithMaxIndexAgrees mapInst self.updates index self.length)
    (hclone : mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone contents[index.val] = ok value) :
    ∃ value back,
      ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back) ∧
      ((mapInst.get self.updates index = ok (some contents[index.val]) ∧ value = contents[index.val]) ∨
       (mapInst.get self.updates index = ok none ∧
        ValueInst.corecloneCloneInst.clone contents[index.val] = ok value)) ∧
      ∀ replacement,
        (back (some replacement)).Represents ValueInst mapInst (contents.set index.val replacement) ∧
        (back (some replacement)).tree = self.tree ∧
        (back (some replacement)).length = self.length :=
  ProgressiveList.get_mut_spec_of_fallback
    ValueInst mapInst self contents index hrep hindex
    (hreads _ _) (hwrites _ _) (hmax _ _) hclone

/-- Complete mutable access for every machine index. A missing index returns
no element and leaves the list unchanged. A present index returns the pending
value or its actual backing clone, and subsequent write-back replaces exactly
that element. Cloning and agreement of write-back lookups and maximum results
are required only for present elements; the missing-handle law applies only out of bounds. -/
theorem ProgressiveList.get_mut_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hwrites : index.val < contents.length → update_map.GetMutWithWriteReads mapInst self.updates index
      (ProgressiveList.backing_get ValueInst mapInst self))
    (hmax : index.val < contents.length →
      update_map.GetMutWithMaxIndexAgrees mapInst self.updates index self.length)
    (hmissing : contents.length ≤ index.val → update_map.GetMutWithMissing mapInst self.updates index)
    (hclone : ∀ old, contents[index.val]? = some old → mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone old = ok value) :
    ∃ value back,
      ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back) ∧
      match value with
      | none => contents[index.val]? = none ∧ back none = self
      | some value =>
        ∃ old, contents[index.val]? = some old ∧
          ((mapInst.get self.updates index = ok (some old) ∧ value = old) ∨
           (mapInst.get self.updates index = ok none ∧
            ValueInst.corecloneCloneInst.clone old = ok value)) ∧
          ∀ replacement,
            (back (some replacement)).Represents ValueInst mapInst (contents.set index.val replacement) ∧
            (back (some replacement)).tree = self.tree ∧
            (back (some replacement)).length = self.length :=
  ProgressiveList.get_mut_total_spec_of_fallback
    ValueInst mapInst self contents index hrep (hreads _ _)
    (fun hindex => hwrites hindex _ _) (fun hindex => hmax hindex _ _)
    (fun hindex => hmissing hindex _ _) hclone

end milhouse.progressive_list
