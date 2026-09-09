import Tree.Rebase.Success
import Tree.ProgressiveTree.Bounds

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Successful comparisons are required only at corresponding binary layers
of these trees. A zero on either side ends rebasing without element calls. -/
def ProgressiveTree.RebaseComparisons {T : Type} (inst : core.cmp.PartialEq T T) :
    ProgressiveTree T → ProgressiveTree T → Prop
  | .ProgressiveNode _ left right, .ProgressiveNode _ baseLeft baseRight =>
      left.RebaseComparisons inst baseLeft ∧ right.RebaseComparisons inst baseRight
  | _, _ => True

theorem ProgressiveTree.rebaseComparisons_of_total {T : Type} (inst : core.cmp.PartialEq T T)
    (heq : ∀ left right, ∃ equal, inst.eq left right = ok equal)
    (hne : ∀ left right, ∃ different, inst.ne left right = ok different)
    (orig base : ProgressiveTree T) : orig.RebaseComparisons inst base := by
  induction orig generalizing base with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base <;> simp only [ProgressiveTree.RebaseComparisons]
    exact ⟨Tree.rebaseComparisons_of_total inst heq hne _ _, ih _⟩

/-- Compatible shapes and representable original layers guarantee successful
rebasing when the compared leaves terminate. All layer arithmetic is derived;
the base needs no capacity bound, and recorded lengths need not match contents. -/
theorem ProgressiveTree.rebase_on_recursive_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32)
    (horig : orig.Shape factor depth.val) (hbase : base.Shape factor depth.val)
    (hfit : orig.Fits factor depth.val)
    (hcompare : orig.RebaseComparisons ValueInst.corecmpPartialEqInst base) :
    ∃ after, ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (.Ok after) := by
  induction orig generalizing base depth with
  | ProgressiveZero =>
    rw [ProgressiveTree.rebase_on_recursive]
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec (.ProgressiveZero : ProgressiveTree T) base
    cases same <;> simp [hpointer, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
  | ProgressiveNode origHash origLeft origRight ih =>
    rw [ProgressiveTree.rebase_on_recursive]
    obtain ⟨same, hpointer, hsame⟩ :=
      triomphe.arc.Arc.ptr_eq_spec (.ProgressiveNode origHash origLeft origRight) base
    clear hsame
    rw [hpointer]
    cases same with
    | true => exact ⟨base, rfl⟩
    | false =>
      simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
        triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
      cases base with
      | ProgressiveZero => exact ⟨.ProgressiveNode origHash origLeft origRight, rfl⟩
      | ProgressiveNode baseHash baseLeft baseRight =>
        cases horig with
        | node _ origLeftShape origRightShape =>
          cases hbase with
          | node _ baseLeftShape baseRightShape =>
            obtain ⟨next, binary, hnext, hbinary, hbinaryVal, hbits⟩ :=
              next_layer_bounds ValueInst hlayout depth hfit.1
            have hnextVal : next.val = depth.val + 1 := by
              have hadd := UScalar.add_equiv depth 1#u32
              rw [hnext] at hadd
              simp at hadd
              exact hadd.2.1
            obtain ⟨start, hstart, _⟩ :=
              ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq depth
            obtain ⟨capacity, hcapacity, _⟩ :=
              ProgressiveTree.capacity_successor_eq ValueInst hlayout.opt_packing_factor_eq hnext
            obtain ⟨origLocal, horigLocal, _⟩ := WP.spec_imp_exists
              (core.cmp.Ord.min.trait_default_Usize.spec (core.num.Usize.saturating_sub origLength start) capacity)
            obtain ⟨baseLocal, hbaseLocal, _⟩ := WP.spec_imp_exists
              (core.cmp.Ord.min.trait_default_Usize.spec (core.num.Usize.saturating_sub baseLength start) capacity)
            have hword : System.Platform.numBits ≤ 2 ^ System.Platform.numBits := by
              rcases System.Platform.numBits_eq with h | h <;> norm_num [h]
            obtain ⟨fullDepth, hfullDepth, hfullDepthVal⟩ := usize_add_succeeds (lt_of_lt_of_le hbits hword)
            obtain ⟨action, hleft⟩ := Tree.rebase_on_success ValueInst origLeft baseLeft
              origLeftShape baseLeftShape (some (origLocal, baseLocal)) fullDepth
              (by omega) (fun _ => by rw [UScalarTy.Usize_numBits_eq]; omega) hcompare.1
            obtain ⟨newRight, hright⟩ := ih baseRight next
              (by simpa only [hnextVal] using origRightShape)
              (by simpa only [hnextVal] using baseRightShape)
              (by simpa only [hnextVal] using hfit.2) hcompare.2
            obtain ⟨leftSame, hleftSame, _⟩ :=
              triomphe.arc.Arc.ptr_eq_spec (applyRebaseAction origLeft action) origLeft
            obtain ⟨rightSame, hrightSame, _⟩ := triomphe.arc.Arc.ptr_eq_spec newRight origRight
            simp only [hstart, hnext, hcapacity, hbinary, hlayout.opt_packing_depth_eq,
              hlayout.unwrap_opt_packing_depth_eq, lift, bind_tc_ok, horigLocal, hbaseLocal,
              hfullDepth, hleft, core.result.Result.Insts.CoreOpsTry.branch]
            cases action <;> cases leftSame <;> cases rightSame <;>
              simp only [applyRebaseAction] at hleftSame <;>
              simp [triomphe.arc.Arc.Insts.CoreCloneClone.clone, hright, hleftSame, hrightSame,
                core.result.Result.Insts.CoreOpsTry.branch, lock_api.rwlock.RwLock.read,
                lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
                lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]

/-- Public progressive rebasing succeeds from shape and original capacity
invariants, without density, clone, or cached-hash assumptions. -/
theorem ProgressiveTree.rebase_on_success {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize)
    (horig : orig.Shape factor 0) (hbase : base.Shape factor 0)
    (hfit : orig.Fits factor 0)
    (hcompare : orig.RebaseComparisons ValueInst.corecmpPartialEqInst base) :
    ∃ after, ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after) :=
  ProgressiveTree.rebase_on_recursive_success ValueInst hlayout orig base origLength baseLength 0#u32
    horig hbase hfit hcompare

end milhouse.progressive_tree
