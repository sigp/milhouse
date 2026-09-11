import Tree.ProgressiveList.Construction.Traits
import Tree.ProgressiveList.CopyOnWrite

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The materialized backing sequence is dense up to the recorded backing
    length, and each progressive layer has representable binary capacity.
    These are the structural premises needed by complete backing traversal. -/
def ProgressiveList.BackingValid {T U : Type} (factor : Option Std.Usize)
    (self : ProgressiveList T U) : Prop :=
  self.tree.Dense factor 0 self.length.val ∧ self.tree.Fits factor 0

/-- Successful empty construction establishes backing validity independently
    of the behavior of the generic default map. -/
theorem ProgressiveList.empty_backing_valid {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (factor : Option Std.Usize)
    {self : ProgressiveList T U} (hempty : ProgressiveList.empty ValueInst mapInst = ok self) :
    self.BackingValid factor := by
  cases hdefault : mapInst.coredefaultDefaultInst.default with
  | fail e =>
    simp [ProgressiveList.empty, ProgressiveTree.empty, triomphe.arc.Arc.new, hdefault] at hempty
  | div =>
    simp [ProgressiveList.empty, ProgressiveTree.empty, triomphe.arc.Arc.new, hdefault] at hempty
  | ok updates =>
    rw [ProgressiveList.empty_eq ValueInst mapInst updates hdefault] at hempty
    cases hempty
    exact ⟨.zero factor 0, trivial⟩

theorem ProgressiveList.default_backing_valid {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (factor : Option Std.Usize)
    {self : ProgressiveList T U}
    (hdefault : ProgressiveList.Insts.CoreDefaultDefault.default ValueInst mapInst = ok self) :
    self.BackingValid factor := by
  rw [ProgressiveList.default_eq_empty] at hdefault
  exact ProgressiveList.empty_backing_valid ValueInst mapInst factor hdefault

/-- Vector construction establishes the traversal invariant without requiring
    iterator-output or default-map laws. -/
theorem ProgressiveList.new_backing_valid {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (values : alloc.vec.Vec T) {self : ProgressiveList T U}
    (hnew : ProgressiveList.new ValueInst mapInst values = ok (core.result.Result.Ok self)) :
    self.BackingValid factor :=
  ProgressiveList.try_from_iter_backing_valid ValueInst mapInst
    (core.iter.traits.collect.IntoIteratorVec T) values hlayout hnew

/-- Pending append leaves the materialized tree and backing length unchanged,
    so it preserves density and representable layer capacities. -/
theorem ProgressiveList.push_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) {factor : Option Std.Usize}
    (hbacking : self.BackingValid factor) {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    pushed.BackingValid factor := by
  cases hlen : ProgressiveList.len ValueInst mapInst self with
  | fail e => simp [ProgressiveList.push, hlen] at hpush
  | div => simp [ProgressiveList.push, hlen] at hpush
  | ok index =>
    obtain ⟨previous, updates, _, rfl⟩ := ProgressiveList.push_success ValueInst mapInst self value index hlen hpush
    exact hbacking

/-- Every mutable write-back preserves backing density and capacity bounds;
    this includes replacements and releasing missing or unchanged values. -/
theorem ProgressiveList.get_mut_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {factor : Option Std.Usize}
    (hbacking : self.BackingValid factor)
    {value : Option T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back)) :
    ∀ replacement, (back replacement).BackingValid factor := by
  obtain ⟨mapBack, _, rfl⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact fun _ => hbacking

/-- Releasing any copy-on-write handle changes only the pending map and
    preserves the complete backing traversal invariant. -/
theorem ProgressiveList.get_cow_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {factor : Option Std.Usize}
    (hbacking : self.BackingValid factor)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ∀ replacement, (back replacement).BackingValid factor := by
  obtain ⟨fallback, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact fun _ => hbacking

end milhouse.progressive_list
