import Tree.BulkUpdate
import Tree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- The two possible actions on one child of a successfully updated node.
    Range answers are recorded exactly; their semantic interpretation is a
    separate update-map law in the recursive content proof. -/
def Tree.BulkChildStep {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (before after : Tree T) (prefix1 offset depth lo hi : Std.Usize)
    (hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)) : Prop :=
  (mapInst.has_any_in_range updates lo hi = ok false ∧ after = before) ∨
  (mapInst.has_any_in_range updates lo hi = ok true ∧
    Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after))

/-- Decompose successful node updates into aligned child windows and the
    actual recursive or preserved-child actions. All checked arithmetic and
    both child error paths are included. Success also forces at least one positive
    child answer, without assuming map range laws. -/
theorem Tree.with_updated_leaves_node_step_selected {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {left right updated : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {oldHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst (.Node oldHash left right) updates
      prefix1 offset depth hashes = ok (core.result.Result.Ok updated)) :
    ∃ nd rightPrefix lo middle stop hash newLeft newRight,
      depth.val = nd.val + 1 ∧
      rightPrefix.val = prefix1.val + subtreeCapacity factor nd.val ∧
      lo.val = prefix1.val + offset.val ∧
      middle.val = rightPrefix.val + offset.val ∧
      stop.val = prefix1.val + offset.val + subtreeCapacity factor depth.val ∧
      updated = Tree.Node hash newLeft newRight ∧
      Tree.BulkChildStep ValueInst mapInst updates left newLeft prefix1 offset nd lo middle hashes ∧
      Tree.BulkChildStep ValueInst mapInst updates right newRight rightPrefix offset nd middle stop hashes ∧
      (mapInst.has_any_in_range updates lo middle = ok true ∨
        mapInst.has_any_in_range updates middle stop = ok true) := by
  unfold Tree.with_updated_leaves at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨opt, hopt, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨hash, hhash, hupdate⟩ := hupdate
  change (if depth > 0#usize then _ else _) = _ at hupdate
  by_cases hpositive : depth > 0#usize
  · rw [if_pos hpositive, hlayout.opt_packing_depth_eq] at hupdate
    simp only [hlayout.unwrap_opt_packing_depth_eq, lift, bind_tc_ok,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
      triomphe.arc.Arc.Insts.CoreCloneClone.clone] at hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨nd, hnd, hupdate⟩ := hupdate
    have hndVal := usize_sub_one_val hnd
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨shift, hshift, hupdate⟩ := hupdate
    have hshiftVal := usize_add_val hshift
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨stride, hstride, hupdate⟩ := hupdate
    have hstrideVal := usize_shift_left_one_val hstride
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨parentShift, hparentShift, hupdate⟩ := hupdate
    have hparentShiftVal := usize_add_val hparentShift
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨width, hwidth, hupdate⟩ := hupdate
    have hwidthVal := usize_shift_left_one_val hwidth
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨subtreeEnd, hsubtreeEnd, hupdate⟩ := hupdate
    have hsubtreeEndVal := usize_add_val hsubtreeEnd
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨lo, hlo, hupdate⟩ := hupdate
    have hloVal := usize_add_val hlo
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨middle, hmiddle, hupdate⟩ := hupdate
    have hmiddleVal := usize_add_val hmiddle
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨bl, hbl, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨stop, hstop, hupdate⟩ := hupdate
    have hstopVal := usize_add_val hstop
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨br, hbr, hupdate⟩ := hupdate
    have hchildCap : subtreeCapacity factor nd.val = 2 ^ shift.val := by
      rw [hlayout.subtreeCapacity_eq_two_pow]
      congr 1
      omega
    have hparentCap : subtreeCapacity factor depth.val = 2 ^ (shift.val + 1) := by
      rw [hlayout.subtreeCapacity_eq_two_pow]
      congr 1
      omega
    have hrightPrefix : (prefix1 ||| stride).val = prefix1.val + subtreeCapacity factor nd.val := by
      rw [usize_or_val, hstrideVal, hchildCap]
      apply or_two_pow_aligned
      rwa [← hparentCap]
    have hstopWindow : stop.val = prefix1.val + offset.val + subtreeCapacity factor depth.val := by
      rw [hstopVal, hsubtreeEndVal, hwidthVal, hparentCap]
      have hshiftEq : parentShift.val = shift.val + 1 := by omega
      rw [hshiftEq]
      omega
    have finish : ∀ newLeft newRight,
        updated = Tree.Node hash newLeft newRight →
        Tree.BulkChildStep ValueInst mapInst updates left newLeft prefix1 offset nd lo middle hashes →
        Tree.BulkChildStep ValueInst mapInst updates right newRight
          (prefix1 ||| stride) offset nd middle stop hashes →
        (mapInst.has_any_in_range updates lo middle = ok true ∨
          mapInst.has_any_in_range updates middle stop = ok true) →
        ∃ nd rightPrefix lo middle stop hash newLeft newRight,
          depth.val = nd.val + 1 ∧
          rightPrefix.val = prefix1.val + subtreeCapacity factor nd.val ∧
          lo.val = prefix1.val + offset.val ∧
          middle.val = rightPrefix.val + offset.val ∧
          stop.val = prefix1.val + offset.val + subtreeCapacity factor depth.val ∧
          updated = Tree.Node hash newLeft newRight ∧
          Tree.BulkChildStep ValueInst mapInst updates left newLeft prefix1 offset nd lo middle hashes ∧
          Tree.BulkChildStep ValueInst mapInst updates right newRight rightPrefix offset nd middle stop hashes ∧
          (mapInst.has_any_in_range updates lo middle = ok true ∨
            mapInst.has_any_in_range updates middle stop = ok true) := by
      intro newLeft newRight htree hleft hright hselected
      exact ⟨nd, prefix1 ||| stride, lo, middle, stop, hash, newLeft, newRight,
        hndVal, hrightPrefix, hloVal, hmiddleVal, hstopWindow, htree, hleft, hright, hselected⟩
    cases bl with
    | false =>
      cases br with
      | false => simp at hupdate
      | true =>
        simp only [Bool.false_eq_true, if_false, if_true] at hupdate
        rw [bind_eq_ok_iff] at hupdate
        obtain ⟨r, hr, hupdate⟩ := hupdate
        cases r with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hupdate
        | Ok newRight =>
          simp [core.result.Result.Insts.CoreOpsTry.branch, Tree.node,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
          exact finish left newRight hupdate.symm (Or.inl ⟨hbl, rfl⟩) (Or.inr ⟨hbr, hr⟩) (Or.inr hbr)
    | true =>
      simp only [if_true] at hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨r, hr, hupdate⟩ := hupdate
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hupdate
      | Ok newLeft =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hupdate
        cases br with
        | false =>
          simp [Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
          exact finish newLeft right hupdate.symm (Or.inr ⟨hbl, hr⟩) (Or.inl ⟨hbr, rfl⟩) (Or.inl hbl)
        | true =>
          simp only [if_true] at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨r1, hr1, hupdate⟩ := hupdate
          cases r1 with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | Ok newRight =>
            simp [Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
            exact finish newLeft newRight hupdate.symm (Or.inr ⟨hbl, hr⟩) (Or.inr ⟨hbr, hr1⟩) (Or.inl hbl)
  · simp [hpositive] at hupdate

/-- The original child-step contract, obtained by forgetting the positive
    answer guaranteed by successful node rebuilding. -/
theorem Tree.with_updated_leaves_node_step {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {left right updated : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {oldHash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
      (alloy_primitives.bits.fixed.FixedBytes 32#usize)}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst (.Node oldHash left right) updates
      prefix1 offset depth hashes = ok (core.result.Result.Ok updated)) :
    ∃ nd rightPrefix lo middle stop hash newLeft newRight,
      depth.val = nd.val + 1 ∧
      rightPrefix.val = prefix1.val + subtreeCapacity factor nd.val ∧
      lo.val = prefix1.val + offset.val ∧
      middle.val = rightPrefix.val + offset.val ∧
      stop.val = prefix1.val + offset.val + subtreeCapacity factor depth.val ∧
      updated = Tree.Node hash newLeft newRight ∧
      Tree.BulkChildStep ValueInst mapInst updates left newLeft prefix1 offset nd lo middle hashes ∧
      Tree.BulkChildStep ValueInst mapInst updates right newRight rightPrefix offset nd middle stop hashes := by
  obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
    hnd, hrightPrefix, hlo, hmiddle, hstop, hafter, hleft, hright, _⟩ :=
    Tree.with_updated_leaves_node_step_selected ValueInst mapInst hlayout halign hupdate
  exact ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
    hnd, hrightPrefix, hlo, hmiddle, hstop, hafter, hleft, hright⟩

end milhouse.tree
