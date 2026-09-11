import Tree.Iter.Packed
import Tree.Iter.Node
import Tree.Iterator

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.iter

/-- A live binary cursor always terminates, returns the root sequence's indexed
    value, advances once, and preserves its invariant. Recursive descent is
    justified by the decreasing number of unsaved path frames. -/
theorem Iter.next_live_spec {T : Type} (ValueInst : Value T)
    {root : tree.Tree T} {depth packingDepth : Std.Usize} {factor : Option Std.Usize}
    {length : utils.Length} {self : Iter T}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hdense : DenseTree factor root depth.val length.val)
    (hbits : depth.val + packingDepth.val ≤ System.Platform.numBits)
    (hvalid : Iter.Valid root depth factor packingDepth length self)
    (hlive : self.index < length) :
    ∃ next, Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst self =
        ok (root.elements[self.index.val]?, next) ∧
      next.index.val = self.index.val + 1 ∧
      Iter.Valid root depth factor packingDepth length next := by
  generalize hm : depth.val + 1 - self.stack.val.length = remaining
  induction remaining using Nat.strong_induction_on generalizing self with
  | h remaining ih =>
    have hpath := @Iter.Valid.path T root depth factor packingDepth length self hvalid
    have hliveVal : self.index.val < length.val := by simpa only [UScalar.lt_equiv] using hlive
    have hnonempty := @Iter.Valid.live T root depth factor packingDepth length self hvalid hliveVal
    obtain ⟨completed, node, hstack⟩ : ∃ completed node, self.stack.val = completed ++ [node] := by
      rcases _root_.List.eq_nil_or_concat self.stack.val with hempty | ⟨completed, node, hstack⟩
      · exact (hnonempty hempty).elim
      · exact ⟨completed, node, by simpa using hstack⟩
    have hpathTop : Path packingDepth.val root depth.val self.index.val (completed ++ [node]) := by
      simpa [hstack] using hpath
    have hpower : leafCapacity factor = 2 ^ packingDepth.val := by
      simpa [subtreeCapacity] using hlayout.subtreeCapacity_eq_two_pow 0
    obtain ⟨htop, hslot⟩ := hpathTop.top completed hpower hdense.shape
    cases node with
    | Zero nodeDepth =>
      have hinside : self.index.val < subtreeCapacity factor depth.val :=
        hliveVal.trans_le hdense.length_le_capacity
      have hrootSlot := hdense.slot_eq_elements_mod self.index.val
      rw [Nat.mod_eq_of_lt hinside] at hrootSlot
      have hnone : root.elements[self.index.val]? = none := by
        rw [← hrootSlot, hslot]
        rfl
      have hmissing := _root_.List.getElem?_eq_none_iff.mp hnone
      have hlength := hdense.elements_length
      omega
    | Leaf value =>
      have hfactor : factor = none := by
        generalize hr : depth.val - completed.length = currentDepth at htop
        cases htop
        rfl
      subst factor
      cases hlayout
      exact Iter.next_leaf_spec ValueInst hdense hvalid completed value hstack hlive
    | PackedLeaf value =>
      have hfactor : ∃ packedFactor, factor = some packedFactor := by
        generalize hr : depth.val - completed.length = currentDepth at htop
        cases htop
        exact ⟨_, rfl⟩
      obtain ⟨packedFactor, rfl⟩ := hfactor
      have hpacked : packedFactor.val = 2 ^ packingDepth.val := by cases hlayout; assumption
      exact Iter.next_packed_spec ValueInst hpacked hdense hvalid completed value hstack hlive
    | Node hash left right =>
      obtain ⟨child, hstep, hindex, hlength, hchild⟩ := Iter.next_node_step ValueInst
        hlayout hdense.shape hbits hvalid completed hash left right hstack hlive
      have hchildPath := @Iter.Valid.path T root depth factor packingDepth length child hchild
      have hbound := hchildPath.length_le
      have hdecrease : depth.val + 1 - child.stack.val.length < remaining := by omega
      obtain ⟨next, hnext, hnextIndex, hnextValid⟩ := ih
        (depth.val + 1 - child.stack.val.length) hdecrease hchild
        (by simpa [hindex] using hlive) rfl
      refine ⟨next, ?_, ?_, hnextValid⟩
      · rw [hstep, hnext, hindex]
      · simpa [hindex] using hnextIndex

end milhouse.iter
