import Tree.ProgressiveTree.Rebase.Requirements
import Tree.ProgressiveTree.Rebase.Steps

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- The two checked depth bounds suffice for advancement, binary conversion,
and packing-depth addition. No bound on a layer's capacity is needed. -/
theorem ProgressiveTree.rebase_depth_success {T : Type} (ValueInst : Value T)
    (depth : Std.U32) (packingDepth : Std.Usize)
    (hnextBound : depth.val + 1 ≤ Std.U32.max)
    (hfullBound : 2 * depth.val + packingDepth.val ≤ Std.Usize.max) :
    ∃ next binary fullDepth,
      depth + 1#u32 = ok next ∧ next.val = depth.val + 1 ∧
      ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary ∧
      binary + packingDepth = ok fullDepth ∧ fullDepth.val = 2 * depth.val + packingDepth.val := by
  obtain ⟨next, hnext, hnextVal⟩ := WP.spec_imp_exists
    (U32.add_spec (x := depth) (y := 1#u32) (by simpa using hnextBound))
  have hcast : (UScalar.cast .Usize depth).val = depth.val := by
    apply UScalar.cast_val_mod_pow_greater_numBits_eq
    simp only [UScalarTy.Usize_numBits_eq, UScalarTy.U32_numBits_eq]
    cases System.Platform.numBits_eq <;> omega
  obtain ⟨binary, hbinary, hbinaryVal⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := 2#usize) (y := UScalar.cast .Usize depth) (by simp [hcast]; omega))
  have hbinaryNat : binary.val = 2 * depth.val := by simpa [hcast] using hbinaryVal
  obtain ⟨fullDepth, hfullDepth, hfullDepthVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := binary) (y := packingDepth) (by omega))
  exact ⟨next, binary, fullDepth, hnext, by simpa using hnextVal,
    (ProgressiveTree.binary_depth_successor_eq ValueInst hnext).trans hbinary,
    hfullDepth, by omega⟩

/-- Every successful progressive call supplies the complete selected input
requirements, retaining saturated capacity arithmetic. No tree shape, capacity
invariant, density, accurate length metadata, or semantic law is assumed. -/
theorem ProgressiveTree.rebase_on_recursive_requirements {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (.Ok after)) :
    orig.RebaseRequirements ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength.val baseLength.val depth.val := by
  induction orig generalizing base after depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode origHash origLeft origRight ih =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same _ _ hstop =>
      exact ProgressiveTree.rebaseRequirements_of_stop ValueInst.corecmpPartialEqInst _ _ _ _ _ _ _ hstop
    | @node _ baseHash _ baseLeft _ baseRight newRight start capacity binary fullDepth origLeftLength baseLeftLength next
        action hstart hnext hcapacity hbinary horigLength hbaseLength hfullDepth hleft hright hpointer =>
      have horigLengthVal := ProgressiveTree.rebase_layer_length_clamped ValueInst hlayout.opt_packing_factor_eq
        hstart hnext hcapacity horigLength
      have hbaseLengthVal := ProgressiveTree.rebase_layer_length_clamped ValueInst hlayout.opt_packing_factor_eq
        hstart hnext hcapacity hbaseLength
      have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
      have hfullDepthVal := usize_add_val hfullDepth
      have hfullDepthNat : fullDepth.val = 2 * depth.val + packingDepth.val := by omega
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hnext] at hadd
      simp at hadd
      have hnextVal : next.val = depth.val + 1 := by omega
      refine fun _ => ⟨by scalar_tac, by scalar_tac, ?_, ?_, ?_⟩
      · simpa only [rebaseLengths, Option.map_some, horigLengthVal, hbaseLengthVal, hfullDepthNat]
          using Tree.rebase_on_geometry ValueInst hleft
      · simpa only [rebaseLengths, Option.map_some, horigLengthVal, hbaseLengthVal, hfullDepthNat]
          using Tree.rebase_on_comparisons ValueInst hleft
      · simpa only [hnextVal] using ih hright

/-- The selected arithmetic, binary geometry, and external element calls
suffice for actual progressive execution, without global shape or capacity
invariants. Every internal success and metadata value is established here. -/
theorem ProgressiveTree.rebase_on_recursive_success_of_requirements {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32)
    (hinputs : orig.RebaseRequirements ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength.val baseLength.val depth.val) :
    ∃ after, ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after) := by
  induction orig generalizing base depth with
  | ProgressiveZero =>
    rw [ProgressiveTree.rebase_on_recursive]
    obtain ⟨same, hpointer, _⟩ := triomphe.arc.Arc.ptr_eq_spec (.ProgressiveZero : ProgressiveTree T) base
    cases same <;> simp [hpointer, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
      triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
  | ProgressiveNode origHash origLeft origRight ih =>
    rw [ProgressiveTree.rebase_on_recursive]
    obtain ⟨same, hpointer, hsame⟩ := triomphe.arc.Arc.ptr_eq_spec (.ProgressiveNode origHash origLeft origRight) base
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
        obtain ⟨hnextBound, hfullBound, hgeometry, hcompare, hrightInputs⟩ := hinputs hpointer
        obtain ⟨next, binary, fullDepth, hnext, hnextVal, hbinary, hfullDepth, hfullDepthNat⟩ :=
          ProgressiveTree.rebase_depth_success ValueInst depth packingDepth hnextBound hfullBound
        obtain ⟨start, hstart, _⟩ := ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq depth
        obtain ⟨capacity, hcapacity, _⟩ := ProgressiveTree.capacity_successor_eq ValueInst hlayout.opt_packing_factor_eq hnext
        obtain ⟨origLocal, horigLocal, _⟩ := WP.spec_imp_exists
          (core.cmp.Ord.min.trait_default_Usize.spec (core.num.Usize.saturating_sub origLength start) capacity)
        obtain ⟨baseLocal, hbaseLocal, _⟩ := WP.spec_imp_exists
          (core.cmp.Ord.min.trait_default_Usize.spec (core.num.Usize.saturating_sub baseLength start) capacity)
        have horigLocalVal := ProgressiveTree.rebase_layer_length_clamped ValueInst hlayout.opt_packing_factor_eq
          hstart hnext hcapacity horigLocal
        have hbaseLocalVal := ProgressiveTree.rebase_layer_length_clamped ValueInst hlayout.opt_packing_factor_eq
          hstart hnext hcapacity hbaseLocal
        obtain ⟨action, hleft⟩ := Tree.rebase_on_success_of_geometry ValueInst origLeft baseLeft
          (some (origLocal, baseLocal)) fullDepth
          (by simpa only [rebaseLengths, Option.map_some, horigLocalVal, hbaseLocalVal, hfullDepthNat] using hgeometry)
          (by simpa only [rebaseLengths, Option.map_some, horigLocalVal, hbaseLocalVal, hfullDepthNat] using hcompare)
        obtain ⟨newRight, hright⟩ := ih baseRight next (by simpa only [hnextVal] using hrightInputs)
        obtain ⟨leftSame, hleftSame, _⟩ := triomphe.arc.Arc.ptr_eq_spec (applyRebaseAction origLeft action) origLeft
        obtain ⟨rightSame, hrightSame, _⟩ := triomphe.arc.Arc.ptr_eq_spec newRight origRight
        simp only [hstart, hnext, hcapacity, hbinary, hlayout.opt_packing_depth_eq,
          hlayout.unwrap_opt_packing_depth_eq, lift, bind_tc_ok, horigLocal, hbaseLocal,
          hfullDepth, hleft, core.result.Result.Insts.CoreOpsTry.branch]
        cases action <;> cases leftSame <;> cases rightSame <;>
          simp only [applyRebaseAction] at hleftSame <;>
          simp [triomphe.arc.Arc.Insts.CoreCloneClone.clone, hright, hleftSame, hrightSame,
            lock_api.rwlock.RwLock.read,
            lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref,
            lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]

/-- At a fixed packing layout, the selected input requirements completely
characterize recursive success on arbitrary progressive trees and metadata. -/
theorem ProgressiveTree.rebase_on_recursive_success_iff_requirements {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32) :
    (∃ after, ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after)) ↔
      orig.RebaseRequirements ValueInst.corecmpPartialEqInst base factor
        packingDepth.val origLength.val baseLength.val depth.val := by
  constructor
  · rintro ⟨after, hrebase⟩
    exact ProgressiveTree.rebase_on_recursive_requirements ValueInst hlayout hrebase
  · exact ProgressiveTree.rebase_on_recursive_success_of_requirements ValueInst hlayout orig base origLength baseLength depth

/-- Public progressive success has the same selected criterion at depth zero,
with no global tree-shape or representable-layer assumption. -/
theorem ProgressiveTree.rebase_on_success_iff_requirements {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) :
    (∃ after, ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after)) ↔
      orig.RebaseRequirements ValueInst.corecmpPartialEqInst base factor
        packingDepth.val origLength.val baseLength.val 0 :=
  ProgressiveTree.rebase_on_recursive_success_iff_requirements ValueInst hlayout orig base origLength baseLength 0#u32

end milhouse.progressive_tree
