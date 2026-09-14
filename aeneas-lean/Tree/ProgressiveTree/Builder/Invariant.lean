import Tree.Builder.Metadata
import Tree.ProgressiveTree.Builder.Contents
import Tree.ProgressiveTree.Builder.Density

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.tree

namespace milhouse.progressive_tree

/-- Completed layers are full, and the current leaf-level binary builder has
    the depth and cached capacity of the next progressive layer. -/
structure ProgressiveTreeBuilder.Geometry {T : Type} (ValueInst : Value T)
    (factor : Option Std.Usize) (self : ProgressiveTreeBuilder T) : Prop where
  current : BuilderInvariant ValueInst self.current
  factor_eq : self.current.packing_factor = factor
  level : self.current.level.val = 0
  binary_depth : self.current.depth.val = 2 * self.subtrees.val.length
  progressive_depth : self.prog_depth.val = self.subtrees.val.length + 1
  capacity : self.capacity = self.current.capacity
  completed : FullLayers factor 0 self.subtrees.val

def ProgressiveTreeBuilder.Valid {T : Type} (ValueInst : Value T)
    (factor : Option Std.Usize) (self : ProgressiveTreeBuilder T) : Prop :=
  self.Geometry ValueInst factor ∧ self.Counts

private theorem new_current_layer {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {depth next : Std.U32} {binary capacity : Std.Usize} {current : Builder T}
    (hnext : depth + 1#u32 = ok next)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hnew : Builder.new ValueInst binary 0#usize = ok (core.result.Result.Ok current))
    (hcapacity : ProgressiveTree.capacity_at_depth ValueInst next = ok capacity) :
    BuilderInvariant ValueInst current ∧ current.packing_factor = factor ∧
      current.level.val = 0 ∧ current.depth.val = 2 * depth.val ∧ capacity = current.capacity := by
  have hinvariant := builder_new_establishes_invariant ValueInst hlayout binary 0#usize
    (Or.inl rfl) (by simp) hnew
  obtain ⟨hdepth, hlevel, _⟩ := Builder.new_parameters ValueInst binary 0#usize hnew
  have hfactor : current.packing_factor = factor := by
    have hquery := (@BuilderInvariant.layout T ValueInst current hinvariant).opt_packing_factor_eq
    rw [hlayout.opt_packing_factor_eq] at hquery
    exact (Result.ok.inj hquery).symm
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  have hdepthVal : current.depth.val = 2 * depth.val := by rw [hdepth, hbinaryVal]
  have hcapacityVal := @BuilderInvariant.builder_capacity_matches T ValueInst current hinvariant
  rw [hfactor, hdepthVal] at hcapacityVal
  obtain ⟨cached, hcached, hcachedVal⟩ := ProgressiveTree.capacity_successor_eq ValueInst
    hlayout.opt_packing_factor_eq hnext
  rw [hcapacity] at hcached
  have heq := Result.ok.inj hcached
  subst cached
  refine ⟨hinvariant, hfactor, by simp [hlevel], hdepthVal, ?_⟩
  apply UScalar.eq_of_val_eq
  have hfit : subtreeCapacity factor (2 * depth.val) ≤ Std.Usize.max := by
    rw [← hcapacityVal]
    scalar_tac
  rw [min_eq_right hfit, ← hcapacityVal] at hcachedVal
  exact hcachedVal

/-- A successful new progressive builder establishes its geometry and both
    counters. The only law supplied by the caller is the element packing layout. -/
theorem ProgressiveTreeBuilder.new_valid {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveTreeBuilder T}
    (hnew : ProgressiveTreeBuilder.new ValueInst = ok (core.result.Result.Ok self)) :
    self.Valid ValueInst factor := by
  refine ⟨?_, (ProgressiveTreeBuilder.new_elements ValueInst hnew).2⟩
  unfold ProgressiveTreeBuilder.new at hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨binary, hbinary, hnew⟩ := hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨status, hcurrent, hnew⟩ := hnew
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hnew
  | Ok current =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hnew
    rw [bind_eq_ok_iff] at hnew
    obtain ⟨capacity, hcapacity, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    obtain ⟨hinvariant, hfactor, hlevel, hdepth, hcapacity⟩ :=
      new_current_layer ValueInst hlayout (depth := 0#u32) rfl hbinary hcurrent hcapacity
    exact ⟨hinvariant, hfactor, hlevel, hdepth, rfl, hcapacity, trivial⟩

private theorem pushTail_geometry {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {self result : ProgressiveTreeBuilder T}
    (hgeometry : self.Geometry ValueInst factor) (value : T)
    (hpush : ProgressiveTreeBuilder.pushTail ValueInst self value =
      ok (core.result.Result.Ok (), result)) :
    result.Geometry ValueInst factor := by
  unfold ProgressiveTreeBuilder.pushTail at hpush
  rw [bind_eq_ok_iff] at hpush
  obtain ⟨⟨status, current⟩, hcurrent, hpush⟩ := hpush
  dsimp! only at hpush
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
  | Ok success =>
    cases success
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, bind_eq_ok_iff] at hpush
    obtain ⟨count, _, length, _, hpush⟩ := hpush
    simp only [ok.injEq, Prod.mk.injEq, true_and] at hpush
    subst result
    have hconfig := Builder.push_configuration ValueInst _ _ hcurrent
    simp only [Builder.configuration, Prod.mk.injEq] at hconfig
    obtain ⟨hdepth, hlevel, hfactor, hpacking, hcapacity⟩ := hconfig
    exact ⟨builder_push_preserves_invariant (@ProgressiveTreeBuilder.Geometry.current T ValueInst factor self hgeometry) (@ProgressiveTreeBuilder.Geometry.level T ValueInst factor self hgeometry) value hcurrent,
      hfactor.trans (@ProgressiveTreeBuilder.Geometry.factor_eq T ValueInst factor self hgeometry), by simpa [hlevel] using (@ProgressiveTreeBuilder.Geometry.level T ValueInst factor self hgeometry),
      by simpa [hdepth] using (@ProgressiveTreeBuilder.Geometry.binary_depth T ValueInst factor self hgeometry), (@ProgressiveTreeBuilder.Geometry.progressive_depth T ValueInst factor self hgeometry),
      (@ProgressiveTreeBuilder.Geometry.capacity T ValueInst factor self hgeometry).trans hcapacity.symm, (@ProgressiveTreeBuilder.Geometry.completed T ValueInst factor self hgeometry)⟩

/-- Successful pushes preserve the complete builder invariant, including the
    completed forest when a full current subtree rolls over to the next layer. -/
theorem ProgressiveTreeBuilder.push_preserves_valid {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {self result : ProgressiveTreeBuilder T}
    (hvalid : self.Valid ValueInst factor) (value : T)
    (hpush : ProgressiveTreeBuilder.push ValueInst self value =
      ok (core.result.Result.Ok (), result)) :
    result.Valid ValueInst factor := by
  obtain ⟨hgeometry, hcounts⟩ := hvalid
  refine ⟨?_, ProgressiveTreeBuilder.push_preserves_counts ValueInst self value hcounts hpush⟩
  unfold ProgressiveTreeBuilder.push at hpush
  split at hpush
  · rename_i hfull
    rw [bind_eq_ok_iff] at hpush
    obtain ⟨depth, hnext, hpush⟩ := hpush
    rw [bind_eq_ok_iff] at hpush
    obtain ⟨binary, hbinary, hpush⟩ := hpush
    rw [bind_eq_ok_iff] at hpush
    obtain ⟨status, hnew, hpush⟩ := hpush
    cases status with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
    | Ok current =>
      simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, core.mem.replace] at hpush
      rw [bind_eq_ok_iff] at hpush
      obtain ⟨status, hfinish, hpush⟩ := hpush
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hpush
      | Ok output =>
        obtain ⟨output, outputDepth, outputLength⟩ := output
        simp! only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨subtrees, hsubtrees, hpush⟩ := hpush
        rw [bind_eq_ok_iff] at hpush
        obtain ⟨capacity, hcapacity, hpush⟩ := hpush
        let prepared := {self with subtrees, current, prog_depth := depth, capacity, count := 0#usize}
        change ProgressiveTreeBuilder.pushTail ValueInst prepared value =
          ok (core.result.Result.Ok (), result) at hpush
        apply pushTail_geometry ValueInst (self := prepared) ?_ value hpush
        have hlayout := @BuilderInvariant.layout T ValueInst self.current (@ProgressiveTreeBuilder.Geometry.current T ValueInst factor self hgeometry)
        rw [(@ProgressiveTreeBuilder.Geometry.factor_eq T ValueInst factor self hgeometry)] at hlayout
        obtain ⟨hcurrent, hfactor, hlevel, hdepth, hcapacity⟩ :=
          new_current_layer ValueInst hlayout hnext hbinary hnew hcapacity
        have hsubtreesVal := vec_push_values hsubtrees
        have hsubtreesLen : subtrees.val.length = self.subtrees.val.length + 1 := by
          simp [hsubtreesVal]
        have hnextVal : depth.val = self.prog_depth.val + 1 := by
          have h := UScalar.add_equiv self.prog_depth 1#u32
          rw [hnext] at h
          simp at h
          omega
        refine ⟨hcurrent, hfactor, hlevel, ?_, ?_, hcapacity, ?_⟩
        · simpa [prepared, hsubtreesLen, (@ProgressiveTreeBuilder.Geometry.progressive_depth T ValueInst factor self hgeometry)] using hdepth
        · simp [prepared, hnextVal, hsubtreesLen, (@ProgressiveTreeBuilder.Geometry.progressive_depth T ValueInst factor self hgeometry)]
        · change FullLayers factor 0 subtrees.val
          rw [hsubtreesVal]
          apply (@ProgressiveTreeBuilder.Geometry.completed T ValueInst factor self hgeometry).append
          obtain ⟨_, houtputDepth, _, hdense⟩ := Builder.finish_spec (@ProgressiveTreeBuilder.Geometry.current T ValueInst factor self hgeometry) hfinish
          have hcapacityMatches := @BuilderInvariant.builder_capacity_matches T ValueInst self.current (@ProgressiveTreeBuilder.Geometry.current T ValueInst factor self hgeometry)
          have hlength : self.current.elements.length = subtreeCapacity factor (2 * self.subtrees.val.length) := by
            have hcount := hcounts.1
            rw [hfull, (@ProgressiveTreeBuilder.Geometry.capacity T ValueInst factor self hgeometry)] at hcount
            rw [(@ProgressiveTreeBuilder.Geometry.factor_eq T ValueInst factor self hgeometry), (@ProgressiveTreeBuilder.Geometry.binary_depth T ValueInst factor self hgeometry)] at hcapacityMatches
            omega
          rw [houtputDepth, (@ProgressiveTreeBuilder.Geometry.factor_eq T ValueInst factor self hgeometry), (@ProgressiveTreeBuilder.Geometry.binary_depth T ValueInst factor self hgeometry), hlength] at hdense
          exact ⟨by simpa using hdense, trivial⟩
  · exact pushTail_geometry ValueInst hgeometry value hpush

end milhouse.progressive_tree
