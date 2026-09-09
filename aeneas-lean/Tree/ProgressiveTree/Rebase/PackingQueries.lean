import Tree.Invariants

open Aeneas Aeneas.Std Result

namespace milhouse.progressive_tree

/-- Actual packing query results used by progressive rebase. This records no
power-of-two, positivity, factor/depth coherence, or tree-layout law. The depth
is exactly the defaulted optional result, including the unpacked zero default. -/
structure RebasePackingQueries {T : Type} (inst : tree_hash.TreeHash T)
    (factor : Option Std.Usize) (depth : Std.Usize) : Prop where
  factor_eq : utils.opt_packing_factor inst = ok factor
  depth_eq : ∃ optionalDepth, utils.opt_packing_depth inst = ok optionalDepth ∧
    core.option.Option.unwrap_or optionalDepth 0#usize = depth

/-- The existing layout law supplies the weaker operational query contract. -/
theorem RebasePackingQueries.of_layout {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {depth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor depth) :
    RebasePackingQueries ValueInst.tree_hashTreeHashInst factor depth :=
  ⟨hlayout.opt_packing_factor_eq,
    ⟨_, hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq⟩⟩

/-- Actual query results determine both metadata values uniquely, without a
factor/depth coherence law. -/
theorem RebasePackingQueries.unique {T : Type} {inst : tree_hash.TreeHash T}
    {factor₁ factor₂ : Option Std.Usize} {depth₁ depth₂ : Std.Usize}
    (left : RebasePackingQueries inst factor₁ depth₁)
    (right : RebasePackingQueries inst factor₂ depth₂) :
    factor₁ = factor₂ ∧ depth₁ = depth₂ := by
  constructor
  · exact Result.ok.inj (left.factor_eq.symm.trans right.factor_eq)
  · obtain ⟨optionalLeft, hleft, hdefaultLeft⟩ := left.depth_eq
    obtain ⟨optionalRight, hright, hdefaultRight⟩ := right.depth_eq
    have heq := Result.ok.inj (hleft.symm.trans hright)
    subst optionalRight
    exact hdefaultLeft.symm.trans hdefaultRight

/-- A successful depth query necessarily completed the actual factor query.
This is derived from the extracted body, without a factor/depth law. -/
theorem rebase_factor_query_of_depth {T : Type} (inst : tree_hash.TreeHash T)
    {optionalDepth : Option Std.Usize}
    (hdepth : utils.opt_packing_depth inst = ok optionalDepth) :
    ∃ factor, utils.opt_packing_factor inst = ok factor := by
  unfold utils.opt_packing_depth at hdepth
  cases hfactor : utils.opt_packing_factor inst with
  | fail error => simp [hfactor] at hdepth
  | div => simp [hfactor] at hdepth
  | ok factor => exact ⟨factor, rfl⟩

/-- Both query results can be recovered from the actual successful depth
query; earlier and repeated factor queries have the same functional result. -/
theorem rebasePackingQueries_of_depth {T : Type} (inst : tree_hash.TreeHash T)
    {optionalDepth : Option Std.Usize}
    (hdepth : utils.opt_packing_depth inst = ok optionalDepth) :
    ∃ factor, RebasePackingQueries inst factor (core.option.Option.unwrap_or optionalDepth 0#usize) := by
  obtain ⟨factor, hfactor⟩ := rebase_factor_query_of_depth inst hdepth
  exact ⟨factor, hfactor, optionalDepth, hdepth, rfl⟩

/-- A returned factor fixes the complete remaining depth computation. Packed
factors retain the actual logarithm call, including its failures/divergence;
unpacked factors skip it. No power-of-two or termination law is assumed. -/
theorem rebase_depth_query_of_factor {T : Type} (inst : tree_hash.TreeHash T)
    {factor : Option Std.Usize} (hfactor : utils.opt_packing_factor inst = ok factor) :
    utils.opt_packing_depth inst =
      (match factor with
      | none => ok none
      | some value => do
        let depth ← utils.int_log value
        ok (some depth)) := by
  cases factor <;> simp [utils.opt_packing_depth, hfactor,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

end milhouse.progressive_tree
