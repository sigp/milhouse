import Tree.BulkUpdate.CloneScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Independent storage and pending laws can be combined over exactly the
same selected binary traversal. -/
theorem Tree.BulkCloneScope.and_iff {T U : Type}
    {S R : packed_leaf.PackedLeaf T → Nat → Prop} {P Q : T → Prop}
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) (depth start : Nat) :
    self.BulkCloneScope (fun leaf start => S leaf start ∧ R leaf start)
      (fun value => P value ∧ Q value) mapInst updates factor depth start ↔
      self.BulkCloneScope S P mapInst updates factor depth start ∧
      self.BulkCloneScope R Q mapInst updates factor depth start := by
  induction depth generalizing self start with
  | zero =>
    cases self <;> simp only [Tree.BulkCloneScope, forall_and] <;> tauto
  | succ depth ih =>
    cases self <;> simp only [Tree.BulkCloneScope, ih, forall_and] <;> tauto

/-- A law on every copied stored value in selected packed leaves. Pending
values impose no condition in this scope. -/
abbrev Tree.BulkStoredCloneOn {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (self : Tree T) (depth start : Nat) : Prop :=
  self.BulkCloneScope (fun leaf _ => ∀ value ∈ leaf.values.val, P value)
    (fun _ => True) mapInst updates factor depth start

/-- Zero padding contributes no stored clone inputs at any binary depth. -/
theorem Tree.BulkStoredCloneOn.zero {T U : Type} (P : T → Prop)
    (mapInst : update_map.UpdateMap U T) (updates : U) (factor : Option Std.Usize)
    (zeroDepth : Std.Usize) (depth start : Nat) :
    (Tree.Zero zeroDepth : Tree T).BulkStoredCloneOn P mapInst updates factor depth start := by
  induction depth generalizing zeroDepth start with
  | zero => simp [Tree.BulkStoredCloneOn, Tree.BulkCloneScope]
  | succ depth ih =>
    constructor <;> intro lo hi _ _ _ <;> exact ih _ _

/-- The total clone law is exactly stored-clone termination together with
identity on retained slots and selected pending values. -/
theorem Tree.BulkCloneLaws.iff_stored_and_retained {T U : Type}
    (cloneInst : core.clone.Clone T) (mapInst : update_map.UpdateMap U T)
    (updates : U) (factor : Option Std.Usize) (self : Tree T) (depth start : Nat) :
    self.BulkCloneLaws cloneInst mapInst updates factor depth start ↔
      self.BulkStoredCloneOn (fun value => ∃ copied, cloneInst.clone value = ok copied)
        mapInst updates factor depth start ∧
      self.BulkRetainedCloneOn (fun value => cloneInst.clone value = ok value)
        mapInst updates factor depth start := by
  unfold Tree.BulkCloneLaws Tree.BulkStoredCloneOn Tree.BulkRetainedCloneOn
  rw [← Tree.BulkCloneScope.and_iff]
  simp only [true_and]

end milhouse.tree
