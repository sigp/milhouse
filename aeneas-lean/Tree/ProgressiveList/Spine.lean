import Tree.ProgressiveList.Mutable
import Tree.ProgressiveTree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The backing spine has the expected binary depths and does not terminate
    before the backing length. This structural invariant is separate from
    logical sequence representation and from binary density. -/
def ProgressiveList.SpineValid {T U : Type} (factor : Option Std.Usize)
    (self : ProgressiveList T U) : Prop :=
  self.tree.Shape factor 0 ∧ self.tree.EndsAfter factor 0 self.length.val

/-- Successful empty construction establishes the backing-spine invariant
    without requiring any semantic law about the default update map. -/
theorem ProgressiveList.empty_spine {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (factor : Option Std.Usize)
    {self : ProgressiveList T U}
    (hempty : ProgressiveList.empty ValueInst mapInst = ok self) :
    self.SpineValid factor := by
  cases hdefault : mapInst.coredefaultDefaultInst.default with
  | fail e =>
    simp [ProgressiveList.empty, progressive_tree.ProgressiveTree.empty,
      triomphe.arc.Arc.new, hdefault] at hempty
  | div =>
    simp [ProgressiveList.empty, progressive_tree.ProgressiveTree.empty,
      triomphe.arc.Arc.new, hdefault] at hempty
  | ok updates =>
    rw [ProgressiveList.empty_eq ValueInst mapInst updates hdefault] at hempty
    cases hempty
    exact ⟨.zero factor 0, by simp [progressive_tree.ProgressiveTree.EndsAfter]⟩

theorem ProgressiveList.default_spine {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (factor : Option Std.Usize)
    {self : ProgressiveList T U}
    (hdefault : ProgressiveList.Insts.CoreDefaultDefault.default ValueInst mapInst = ok self) :
    self.SpineValid factor := by
  rw [ProgressiveList.default_eq_empty] at hdefault
  exact ProgressiveList.empty_spine ValueInst mapInst factor hdefault

/-- Push changes only the pending map. Its successful result supplies the
    required length evaluation; no extra map or capacity premise is needed. -/
theorem ProgressiveList.push_preserves_spine {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T) {factor : Option Std.Usize}
    (hspine : self.SpineValid factor) {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    pushed.SpineValid factor := by
  cases hlen : ProgressiveList.len ValueInst mapInst self with
  | fail e => simp [ProgressiveList.push, hlen] at hpush
  | div => simp [ProgressiveList.push, hlen] at hpush
  | ok index =>
    obtain ⟨previous, updates, _, rfl⟩ :=
      ProgressiveList.push_success ValueInst mapInst self value index hlen hpush
    exact hspine

/-- Every mutable write-back preserves the backing spine, including replacing
    the element, returning it unchanged, and returning `none`. -/
theorem ProgressiveList.get_mut_preserves_spine {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) {factor : Option Std.Usize}
    (hspine : self.SpineValid factor)
    {value : Option T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back)) :
    ∀ replacement, (back replacement).SpineValid factor := by
  obtain ⟨mapBack, _, rfl⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact fun _ => hspine

end milhouse.progressive_list
