import Tree.BulkUpdate.Skipped

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- Successful binary rebuilding preserves every slot in each reached range
answered false. Layout and prefix alignment identify the actual windows;
no input shape, density, capacity, offset alignment, range, clone, or
termination law is assumed. -/
theorem Tree.with_updated_leaves_skipped_slots {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after))
    {lo hi : Std.Usize}
    (hquery : BulkRangeQueried mapInst updates factor depth.val (prefix1.val + offset.val) lo hi)
    (hfalse : mapInst.has_any_in_range updates lo hi = ok false)
    {query : Nat} (hlo : lo.val ≤ query) (hhi : query < hi.val) :
    after.slot factor depth.val (query - offset.val) = before.slot factor depth.val (query - offset.val) := by
  have aux : ∀ (treeDepth : Nat) (depth : Std.Usize) (before after : Tree T) (prefix1 : Std.Usize),
      depth.val = treeDepth → prefix1.val % subtreeCapacity factor treeDepth = 0 →
      Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes = ok (.Ok after) →
      ∀ (lo hi : Std.Usize), BulkRangeQueried mapInst updates factor treeDepth (prefix1.val + offset.val) lo hi →
      mapInst.has_any_in_range updates lo hi = ok false → lo.val ≤ query → query < hi.val →
      after.slot factor treeDepth (query - offset.val) = before.slot factor treeDepth (query - offset.val) := by
    intro treeDepth
    induction treeDepth with
    | zero =>
      intro _ _ _ _ _ _ _ _ _ hquery
      cases hquery
    | succ child ih =>
      intro depth before after prefix1 hdepth halign hupdate
      have node_slots : ∀ hash left right,
          Tree.with_updated_leaves ValueInst mapInst (.Node hash left right) updates
            prefix1 offset depth hashes = ok (.Ok after) →
          ∀ (lo hi : Std.Usize), BulkRangeQueried mapInst updates factor (child + 1) (prefix1.val + offset.val) lo hi →
          mapInst.has_any_in_range updates lo hi = ok false → lo.val ≤ query → query < hi.val →
          after.slot factor (child + 1) (query - offset.val) =
            (Tree.Node hash left right).slot factor (child + 1) (query - offset.val) := by
        intro oldHash left right hnode queryLo queryHi hquery hfalse hqueryLo hqueryHi
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
        cases hquery with
        | left_here hstart hstop =>
          have heqLo : queryLo = lo := by scalar_tac
          have heqHi : queryHi = middle := by scalar_tac
          subst queryLo
          subst queryHi
          rcases leftStep with ⟨_, rfl⟩ | ⟨htrue, _⟩
          · rw [Tree.slot_node_left_of_aligned halign (by omega) (by omega),
              Tree.slot_node_left_of_aligned halign (by omega) (by omega)]
          · rw [hfalse] at htrue
            cases htrue
        | right_here hstart hstop =>
          have heqLo : queryLo = middle := by scalar_tac
          have heqHi : queryHi = stop := by scalar_tac
          subst queryLo
          subst queryHi
          rcases rightStep with ⟨_, rfl⟩ | ⟨htrue, _⟩
          · rw [Tree.slot_node_right_of_aligned halign (by omega) (by omega),
              Tree.slot_node_right_of_aligned halign (by omega) (by omega)]
          · rw [hfalse] at htrue
            cases htrue
        | @left_tail _ _ selectedLo selectedHi _ _ hstart hstop hselected htail =>
          have heqLo : selectedLo = lo := by scalar_tac
          have heqHi : selectedHi = middle := by scalar_tac
          subst selectedLo
          subst selectedHi
          have hbounds := htail.bounds
          rw [Tree.slot_node_left_of_aligned halign (by omega) (by omega),
            Tree.slot_node_left_of_aligned halign (by omega) (by omega)]
          rcases leftStep with ⟨hempty, _⟩ | ⟨_, hleft⟩
          · rw [hselected] at hempty
            cases hempty
          · exact ih nd left newLeft prefix1 hndDepth halignLeft hleft
              queryLo queryHi htail hfalse hqueryLo hqueryHi
        | @right_tail _ _ selectedLo selectedHi _ _ hstart hstop hselected htail =>
          have heqLo : selectedLo = middle := by scalar_tac
          have heqHi : selectedHi = stop := by scalar_tac
          subst selectedLo
          subst selectedHi
          have hbounds := htail.bounds
          rw [Tree.slot_node_right_of_aligned halign (by omega) (by omega),
            Tree.slot_node_right_of_aligned halign (by omega) (by omega)]
          rcases rightStep with ⟨hempty, _⟩ | ⟨_, hright⟩
          · rw [hselected] at hempty
            cases hempty
          · apply ih nd right newRight rightPrefix hndDepth halignRight hright
              queryLo queryHi ?_ hfalse hqueryLo hqueryHi
            simpa only [hrightPrefix', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
      cases before with
      | Node hash left right => exact node_slots hash left right hupdate
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
          intro queryLo queryHi hquery hfalse hqueryLo hqueryHi
          have h := node_slots _ _ _ hupdate queryLo queryHi hquery hfalse hqueryLo hqueryHi
          exact h.trans (by simp [Tree.slot])
        · simp [hsame] at hupdate
  exact aux depth.val depth before after prefix1 rfl halign hupdate lo hi hquery hfalse hlo hhi

end milhouse.tree
