import Tree.BulkUpdate.StoredCloneScope
import Tree.BulkUpdate.Node
import Tree.PackedLeaf.BulkUpdateClones

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Successful binary rebuilding certifies termination of all selected stored
clones, including copies later overwritten. Layout and prefix alignment identify
the selected windows; no shape, density, capacity, offset alignment, range,
lookup-termination, or clone law is assumed. -/
theorem Tree.with_updated_leaves_stored_clones_terminate {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after)) :
    before.BulkStoredCloneOn (fun value => ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied)
      mapInst updates factor depth.val (prefix1.val + offset.val) := by
  have aux : ∀ (treeDepth : Nat) (depth : Std.Usize) (before after : Tree T) (prefix1 : Std.Usize),
      depth.val = treeDepth → prefix1.val % subtreeCapacity factor treeDepth = 0 →
      Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes = ok (.Ok after) →
      before.BulkStoredCloneOn (fun value => ∃ copied, ValueInst.corecloneCloneInst.clone value = ok copied)
        mapInst updates factor treeDepth (prefix1.val + offset.val) := by
    intro treeDepth
    induction treeDepth with
    | zero =>
      intro depth before after prefix1 hdepth _ hupdate
      cases before with
      | Leaf _ => simp [Tree.BulkStoredCloneOn, Tree.BulkCloneScope]
      | Node _ _ _ => simp [Tree.BulkStoredCloneOn, Tree.BulkCloneScope]
      | Zero _ => exact Tree.BulkStoredCloneOn.zero _ _ _ _ _ _ _
      | PackedLeaf leaf =>
        have hz : depth = 0#usize := by scalar_tac
        subst depth
        constructor
        · unfold Tree.with_updated_leaves at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨opt, _, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨hash, _, hupdate⟩ := hupdate
          change (prefix1 + offset >>= _) = _ at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨start, _, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨result, hresult, _⟩ := hupdate
          exact packed_leaf.PackedLeaf.update_stored_clones_terminate
            ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst mapInst hresult
        · intro _ _ _ _ _
          trivial
    | succ child ih =>
      intro depth before after prefix1 hdepth halign hupdate
      cases before with
      | Leaf _ =>
        constructor <;> intro lo hi _ _ _ <;> exact Tree.BulkStoredCloneOn.zero _ _ _ _ _ _ _
      | PackedLeaf _ =>
        constructor <;> intro lo hi _ _ _ <;> exact Tree.BulkStoredCloneOn.zero _ _ _ _ _ _ _
      | Zero _ => exact Tree.BulkStoredCloneOn.zero _ _ _ _ _ _ _
      | Node oldHash left right =>
        obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
          hnd, hrightPrefix, hlo, hmiddle, hstop, _, leftStep, rightStep⟩ :=
          Tree.with_updated_leaves_node_step ValueInst mapInst hlayout
            (by simpa only [hdepth] using halign) hupdate
        have hndDepth : nd.val = child := by omega
        have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
          simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
        have hrightPrefix' : rightPrefix.val = prefix1.val + subtreeCapacity factor child := by
          simpa only [hndDepth] using hrightPrefix
        have hstop' : stop.val = prefix1.val + offset.val + subtreeCapacity factor (child + 1) := by
          simpa only [hdepth] using hstop
        have halignLeft : prefix1.val % subtreeCapacity factor child = 0 := by
          apply mod_half_eq_zero
          rwa [← hcapacity]
        have halignRight : rightPrefix.val % subtreeCapacity factor child = 0 := by
          rw [hrightPrefix', Nat.add_mod_right]
          exact halignLeft
        constructor
        · intro queryLo queryHi hqueryLo hqueryHi hselected
          have heqLo : queryLo = lo := by scalar_tac
          have heqHi : queryHi = middle := by scalar_tac
          subst queryLo
          subst queryHi
          rcases leftStep with ⟨hempty, _⟩ | ⟨_, hleft⟩
          · rw [hselected] at hempty
            cases hempty
          · exact ih nd left newLeft prefix1 hndDepth halignLeft hleft
        · intro queryLo queryHi hqueryLo hqueryHi hselected
          have heqLo : queryLo = middle := by scalar_tac
          have heqHi : queryHi = stop := by scalar_tac
          subst queryLo
          subst queryHi
          rcases rightStep with ⟨hempty, _⟩ | ⟨_, hright⟩
          · rw [hselected] at hempty
            cases hempty
          · simpa only [hrightPrefix', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih nd right newRight rightPrefix hndDepth halignRight hright
  exact aux depth.val depth before after prefix1 rfl halign hupdate

end milhouse.tree
