import Tree.BulkUpdate.Node
import Tree.UpdateMap.Range

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Contents of a bulk-update result within its assigned window. Pending
    values override existing slots; missing map entries preserve them. The
    offset maps binary-tree indices to container-wide update-map keys. -/
def Tree.BulkContents {T U : Type} (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (before after : Tree T) (depth start offset : Nat) : Prop :=
  ∀ (query : Std.Usize) (pending : Option T), mapInst.get updates query = ok pending →
    start + offset ≤ query.val → query.val < start + offset + subtreeCapacity factor depth →
    after.slot factor depth (query.val - offset) =
      pending.or (before.slot factor depth (query.val - offset))

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private def zeroBit {T : Type} : Tree T → Nat
  | .Zero _ => 1
  | _ => 0

private theorem zeroBit_le_one {T : Type} (self : Tree T) : zeroBit self ≤ 1 := by
  cases self <;> simp [zeroBit]

/-- At an unpacked leaf, the window contains exactly the consumed update key. -/
theorem Tree.bulkContents_of_leaf_value {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {before : Tree T}
    {after : leaf.Leaf T} {index prefix1 offset : Std.Usize}
    (hindex : prefix1 + offset = ok index)
    (hget : mapInst.get updates index = ok (some after.value)) :
    Tree.BulkContents mapInst updates none before (.Leaf after) 0 prefix1.val offset.val := by
  intro query pending hquery hlo hhi
  have hindexVal := usize_add_val hindex
  simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at hhi
  have heq : query = index := by scalar_tac
  subst query
  rw [hget] at hquery
  cases hquery
  rfl

/-- Lift packed-leaf bulk-update contents through the global offset used by
    binary-tree updates. Both starts are aligned to the packing factor. -/
theorem Tree.bulkContents_of_packed_update {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    {updates : U} {before after : packed_leaf.PackedLeaf T}
    {factor prefix1 offset start : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    (hfactor : ValueInst.tree_hashTreeHashInst.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0) (hoffset : offset.val % factor.val = 0)
    (hstart : prefix1 + offset = ok start)
    (hupdate : packed_leaf.PackedLeaf.update ValueInst.tree_hashTreeHashInst
      ValueInst.corecloneCloneInst mapInst before start hash updates = ok (core.result.Result.Ok after)) :
    Tree.BulkContents mapInst updates (some factor) (.PackedLeaf before) (.PackedLeaf after)
      0 prefix1.val offset.val := by
  intro query pending hquery hlo hhi
  have hstartVal := usize_add_val hstart
  simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at hhi
  have hstartAlign : start.val % factor.val = 0 := by simp [hstartVal, Nat.add_mod, halign, hoffset]
  have hmod : (query.val - offset.val) % factor.val = query.val - start.val := by
    rw [mod_eq_sub_of_aligned halign (by omega) (by omega)]
    omega
  have hread := packed_leaf.PackedLeaf.get_after_update hclone hfactor hstartAlign
    (by omega) (by omega) hquery hupdate
  simpa only [Tree.slot, leafCapacity, hmod] using hread

end milhouse.tree
