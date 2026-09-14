import Tree.BulkUpdate.Node
import Tree.BulkUpdate.RangeScope
import Tree.BulkUpdate.Nonempty
import Tree.UpdateMap.RangeExtent

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- A successful binary update with dense output can select only windows
inside its final occupied prefix. Actual selected children rebuild to nonzero
trees, hence have positive dense length. No input invariant, range-value law,
clone law, offset alignment, capacity, or termination assumption is needed. -/
theorem Tree.with_updated_leaves_range_selection {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize} {length : Nat}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after))
    (hdense : DenseTree factor after depth.val length) :
    BulkRangeOn (update_map.RangeSelectsInsideAt mapInst updates (prefix1.val + offset.val + length))
      mapInst updates factor depth.val (prefix1.val + offset.val) := by
  have aux : ∀ (treeDepth : Nat) (depth : Std.Usize) (before after : Tree T)
      (prefix1 : Std.Usize) (length : Nat),
      depth.val = treeDepth → prefix1.val % subtreeCapacity factor treeDepth = 0 →
      Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes = ok (.Ok after) →
      DenseTree factor after treeDepth length →
      BulkRangeOn (update_map.RangeSelectsInsideAt mapInst updates (prefix1.val + offset.val + length))
        mapInst updates factor treeDepth (prefix1.val + offset.val) := by
    intro treeDepth
    induction treeDepth with
    | zero =>
      intro _ _ _ _ _ _ _ _ _ _ _ hquery
      cases hquery
    | succ child ih =>
      intro depth before after prefix1 length hdepth halign hupdate hdense
      have node_selection : ∀ hash left right,
          Tree.with_updated_leaves ValueInst mapInst (.Node hash left right) updates
            prefix1 offset depth hashes = ok (.Ok after) →
          DenseTree factor after (child + 1) length →
          BulkRangeOn (update_map.RangeSelectsInsideAt mapInst updates (prefix1.val + offset.val + length))
            mapInst updates factor (child + 1) (prefix1.val + offset.val) := by
        intro oldHash left right hnode hdense queryLo queryHi hquery htrue
        obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
          hnd, hrightPrefix, hlo, hmiddle, hstop, rfl, leftStep, rightStep⟩ :=
          Tree.with_updated_leaves_node_step ValueInst mapInst hlayout
            (by simpa only [hdepth] using halign) hnode
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
        cases hdense with
        | @node _ _ _ _ _ leftLength rightLength hleftDense hrightDense hleftPos hfull =>
          cases hquery with
          | left_here hstart hstop => omega
          | right_here hstart hstop =>
            have heqLo : queryLo = middle := by scalar_tac
            have heqHi : queryHi = stop := by scalar_tac
            subst queryLo
            subst queryHi
            rcases rightStep with ⟨hfalse, _⟩ | ⟨_, hright⟩
            · rw [htrue] at hfalse
              cases hfalse
            · have hpos := Tree.with_updated_leaves_dense_length_pos ValueInst mapInst hright hrightDense
              have hleftFull := hfull hpos
              omega
          | @left_tail _ _ selectedLo selectedHi _ _ hstart hstop hselected htail =>
            have heqLo : selectedLo = lo := by scalar_tac
            have heqHi : selectedHi = middle := by scalar_tac
            subst selectedLo
            subst selectedHi
            rcases leftStep with ⟨hfalse, _⟩ | ⟨_, hleft⟩
            · rw [hselected] at hfalse
              cases hfalse
            · have hin := ih nd left newLeft prefix1 leftLength hndDepth halignLeft hleft
                hleftDense queryLo queryHi htail htrue
              omega
          | @right_tail _ _ selectedLo selectedHi _ _ hstart hstop hselected htail =>
            have heqLo : selectedLo = middle := by scalar_tac
            have heqHi : selectedHi = stop := by scalar_tac
            subst selectedLo
            subst selectedHi
            rcases rightStep with ⟨hfalse, _⟩ | ⟨_, hright⟩
            · rw [hselected] at hfalse
              cases hfalse
            · have hpos := Tree.with_updated_leaves_dense_length_pos ValueInst mapInst hright hrightDense
              have hleftFull := hfull hpos
              have htail' : BulkRangeQueried mapInst updates factor child
                  (rightPrefix.val + offset.val) queryLo queryHi := by
                simpa only [hrightPrefix', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
              have hin := ih nd right newRight rightPrefix rightLength hndDepth halignRight hright
                hrightDense queryLo queryHi htail' htrue
              omega
      cases before with
      | Node hash left right => exact node_selection hash left right hupdate hdense
      | Leaf leaf =>
        have hz := (Tree.with_updated_leaves_leaf_cloned ValueInst mapInst hupdate).1
        rw [hz] at hdepth
        simp at hdepth
      | PackedLeaf leaf =>
        unfold Tree.with_updated_leaves at hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨opt, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨hash, _, hupdate⟩ := hupdate
        have hz : depth ≠ 0#usize := by scalar_tac
        simp [hz] at hupdate
      | Zero oldDepth =>
        unfold Tree.with_updated_leaves at hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨opt, _, hupdate⟩ := hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨hash, _, hupdate⟩ := hupdate
        dsimp only at hupdate
        by_cases hsame : oldDepth = depth
        · have hz : depth ≠ 0#usize := by scalar_tac
          rw [if_pos hsame, if_neg hz, bind_eq_ok_iff] at hupdate
          obtain ⟨nd, _, hupdate⟩ := hupdate
          simp only [Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
            Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
            bind_tc_ok] at hupdate
          exact node_selection _ _ _ hupdate hdense
        · simp [hsame] at hupdate
  exact aux depth.val depth before after prefix1 length rfl halign hupdate hdense

/-- Clipping a global occupied prefix to a binary window gives the same
necessary positive-selection condition, even when the root lies beyond the
logical end. No global capacity bound or root-positivity law is assumed. -/
theorem Tree.with_updated_leaves_range_selection_of_prefix {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize} {newLength : Nat}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after))
    (hdense : DenseTree factor after depth.val
      (min (newLength - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val))) :
    BulkRangeOn (update_map.RangeSelectsInsideAt mapInst updates newLength)
      mapInst updates factor depth.val (prefix1.val + offset.val) := by
  intro lo hi hquery htrue
  have hbounds := hquery.bounds
  have hin := Tree.with_updated_leaves_range_selection ValueInst mapInst hlayout halign hupdate hdense
    lo hi hquery htrue
  omega

end milhouse.tree
