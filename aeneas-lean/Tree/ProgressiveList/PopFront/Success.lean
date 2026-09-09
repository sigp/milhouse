import Tree.ProgressiveList.PopFront.Contents
import Tree.ProgressiveList.PopFront.BuilderTotal
import Tree.ProgressiveTree.Builder.New
import Tree.ProgressiveTree.Builder.FinishSuccess

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Nonzero removal succeeds, records the retained count, and rebuilds valid
backing from terminating clones of retained values. Clone results may change
those values, and the new default map needs no semantic laws. Actual iterator
construction, streaming pushes, and finalization are proved internally. -/
theorem ProgressiveList.pop_front_nonzero_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (n : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hbacking : self.BackingValid factor)
    (hnonzero : n ≠ 0#usize) (hbound : n.val ≤ contents.length)
    (hclone : ∀ value ∈ contents.drop n.val,
      ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
    (hfits : ProgressiveTree.LengthFits factor (contents.drop n.val).length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ result, ProgressiveList.pop_front ValueInst mapInst self n =
      ok (core.result.Result.Ok (), result) ∧
      result.length.val = (contents.drop n.val).length ∧ result.BackingValid factor ∧
      result.updates = updates := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  have hindex : ¬ n > length := by change ¬ length.val < n.val; omega
  obtain ⟨cursor, hiter, _, _, hyields⟩ := ProgressiveList.iter_from_spec ValueInst mapInst hlayout
    self contents n hrep hbacking.1 hbacking.2 hbound
  obtain ⟨initial, hnew, hvalid, _, hzero⟩ := ProgressiveTreeBuilder.new_spec ValueInst hlayout
  obtain ⟨built, hextend⟩ := ProgressiveListIter.extend_builder_success ValueInst mapInst
    cursor initial (contents.drop n.val) hyields hclone hvalid
    (by simpa only [hzero, Nat.zero_add] using hfits)
  have hvalidBuilt := ProgressiveListIter.extend_builder_preserves_valid
    ValueInst mapInst cursor initial hvalid hextend
  have hcount := ProgressiveListIter.extend_builder_length ValueInst mapInst cursor initial
    (contents.drop n.val) hyields hextend
  obtain ⟨output, hfinish, _, hdense, hcapacity⟩ :=
    ProgressiveTreeBuilder.finish_total_spec ValueInst built hvalidBuilt
  refine ⟨{ tree := output, length := built.length, updates }, ?_, ?_, ⟨hdense, hcapacity⟩, rfl⟩
  · simp! only [ProgressiveList.pop_front, hnonzero, ↓reduceIte, hlen, hindex, hiter, hnew,
      hextend, hfinish, core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new,
      hdefault, bind_tc_ok]
  · simpa only [hzero, Nat.zero_add] using hcount

end milhouse.progressive_list
