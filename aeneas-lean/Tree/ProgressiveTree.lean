import Tree.Lemmas
import Tree.Roundtrip

open Aeneas Aeneas.Std Result
open milhouse

set_option maxHeartbeats 2000000

namespace milhouse.progressive_tree

/-- The binary subtree selected by a progressive lookup, together with its
    local index and binary depth. This separates spine routing from the
    already verified binary-tree operations. It retains checked arithmetic
    and saturation from the Rust lookup, including their failure behavior. -/
def ProgressiveTree.locate {T : Type} (ValueInst : Value T)
    (self : ProgressiveTree T) (index : Std.Usize) (prog_depth : Std.U32) :
    Result (Option (tree.Tree T × Std.Usize × Std.Usize)) := do
  match self with
  | .ProgressiveZero => ok none
  | .ProgressiveNode _ left right =>
    let next ← prog_depth + 1#u32
    let stop ← ProgressiveTree.total_capacity_at_depth ValueInst next
    if index < stop then
      let start ← ProgressiveTree.total_capacity_at_depth ValueInst prog_depth
      let depth ← ProgressiveTree.prog_depth_to_binary_depth ValueInst next
      ok (some (left, core.num.Usize.saturating_sub index start, depth))
    else
      right.locate ValueInst index next

/-- Progressive lookup is precisely spine routing followed by binary-tree
    lookup. No density, index bound, or successful-arithmetic hypothesis is
    needed: both sides have the same behavior on malformed inputs too. -/
theorem ProgressiveTree.get_recursive_eq_locate {T : Type}
    (ValueInst : Value T) (self : ProgressiveTree T)
    (index : Std.Usize) (prog_depth : Std.U32) :
    ProgressiveTree.get_recursive ValueInst self index prog_depth = (do
      let selected ← self.locate ValueInst index prog_depth
      match selected with
      | none => ok none
      | some (binary, local_index, depth) =>
        let opd ← utils.opt_packing_depth ValueInst.tree_hashTreeHashInst
        tree.Tree.get_recursive ValueInst binary local_index depth
          (core.option.Option.unwrap_or opd 0#usize)) := by
  induction self generalizing prog_depth with
  | ProgressiveZero =>
    rw [ProgressiveTree.get_recursive, ProgressiveTree.locate]
    rfl
  | ProgressiveNode hash left right ih =>
    rw [ProgressiveTree.get_recursive, ProgressiveTree.locate]
    cases prog_depth + 1#u32 with
    | fail e => simp
    | div => simp
    | ok next =>
      simp only [bind_tc_ok]
      cases ProgressiveTree.total_capacity_at_depth ValueInst next with
      | fail e => simp
      | div => simp
      | ok stop =>
        simp only [bind_tc_ok]
        by_cases hi : index < stop
        · simp only [if_pos hi]
          cases ProgressiveTree.total_capacity_at_depth ValueInst prog_depth with
          | fail e => simp
          | div => simp
          | ok start =>
            simp only [bind_tc_ok, lift]
            cases ProgressiveTree.prog_depth_to_binary_depth ValueInst next with
            | fail e => simp
            | div => simp
            | ok depth =>
              simp [triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
        · simpa only [if_neg hi, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
            bind_tc_ok] using ih next

end milhouse.progressive_tree
