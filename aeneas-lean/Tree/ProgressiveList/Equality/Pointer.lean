import Tree.ProgressiveList.Equality.Correctness

open Aeneas Aeneas.Std Result

namespace milhouse.progressive_list

/-- Shared backing bypasses every element comparison. Different recorded
lengths return false without consulting the maps; equal lengths return the
negation of the actual pending-map inequality, including its failure or
divergence. No element, map, clone, packing, or representation law is needed. -/
theorem ProgressiveList.partial_eq_of_tree_ptr_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (mapEqInst : core.cmp.PartialEq U U) (self other : ProgressiveList T U)
    (hpointer : triomphe.arc.Arc.ptr_eq self.tree other.tree = ok true) :
    ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq
      ValueInst mapInst ValueInst mapInst mapEqInst self other =
      if self.length = other.length then do
        let different ← mapEqInst.ne self.updates other.updates
        ok (!different)
      else ok false := by
  have htree : progressive_tree.ProgressiveTree.arc_eq ValueInst self.tree other.tree = ok true := by
    rw [progressive_tree.ProgressiveTree.arc_eq, hpointer]
    rfl
  by_cases hlength : self.length = other.length
  · cases hmap : mapEqInst.ne self.updates other.updates with
    | fail error | div =>
      simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree,
        core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        utils.Length.Insts.CoreCmpPartialEqLength.eq, hlength, hmap]
    | ok different =>
      cases different <;>
        simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree,
          core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
          utils.Length.Insts.CoreCmpPartialEqLength.eq, hlength, hmap]
  · simp [ProgressiveList.Insts.CoreCmpPartialEqProgressiveList.eq, htree,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      utils.Length.Insts.CoreCmpPartialEqLength.eq, hlength]

end milhouse.progressive_list
