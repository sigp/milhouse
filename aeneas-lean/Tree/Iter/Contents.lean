import Tree.Iter.Next

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.iter

/-- A valid binary cursor enumerates exactly the root sequence after its current
    index, then returns `none`. This proves finite traversal, including empty
    suffixes and starting indices beyond the recorded length. -/
theorem Iter.yields_suffix {T : Type} (ValueInst : Value T)
    {root : tree.Tree T} {depth packingDepth : Std.Usize} {factor : Option Std.Usize}
    {length : utils.Length} {self : Iter T}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hdense : DenseTree factor root depth.val length.val)
    (hbits : depth.val + packingDepth.val ≤ System.Platform.numBits)
    (hvalid : Iter.Valid root depth factor packingDepth length self) :
    IteratorYields (Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
      self (root.elements.drop self.index.val) := by
  generalize hm : length.val - self.index.val = remaining
  induction remaining using Nat.strong_induction_on generalizing self with
  | h remaining ih =>
    have hrootLength := hdense.elements_length
    by_cases hlive : self.index < length
    · have hliveVal : self.index.val < length.val := by simpa only [UScalar.lt_equiv] using hlive
      obtain ⟨next, hnext, hindex, hnextValid⟩ := Iter.next_live_spec ValueInst hlayout hdense hbits hvalid hlive
      have hinside : self.index.val < root.elements.length := by omega
      rw [_root_.List.drop_eq_getElem_cons hinside]
      refine IteratorYields.cons (rest := next) ?_ ?_
      · simpa only [_root_.List.getElem?_eq_getElem hinside] using hnext
      · have hdecrease : length.val - next.index.val < remaining := by omega
        have htail := ih (length.val - next.index.val) hdecrease hnextValid rfl
        simpa [hindex] using htail
    · have hlength := @Iter.Valid.length_eq T root depth factor packingDepth length self hvalid
      have hexhausted : self.length ≤ self.index := by rw [hlength]; exact le_of_not_gt hlive
      have hbound : root.elements.length ≤ self.index.val := by
        have hle : length.val ≤ self.index.val := by simpa only [UScalar.le_equiv] using (le_of_not_gt hlive)
        omega
      rw [_root_.List.drop_eq_nil_of_le hbound]
      exact IteratorYields.nil (Iter.next_exhausted ValueInst self hexhausted)

/-- Constructing a binary iterator succeeds and its actual `next` calls yield
    precisely the requested suffix of the dense tree. The constructor supplies
    the cursor invariant; no iterator-output or termination premise is assumed. -/
theorem Iter.from_index_yields {T : Type} (ValueInst : Value T)
    {root : tree.Tree T} {depth packingDepth : Std.Usize} {factor : Option Std.Usize}
    {length : utils.Length}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hdense : DenseTree factor root depth.val length.val)
    (hbits : depth.val + packingDepth.val ≤ System.Platform.numBits)
    (index : Std.Usize) :
    ∃ self, Iter.from_index ValueInst index root depth length = ok self ∧
      IteratorYields (Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
        self (root.elements.drop index.val) := by
  obtain ⟨self, hfrom, hindex, _, hvalid⟩ := Iter.from_index_spec ValueInst hlayout index root depth length
  exact ⟨self, hfrom, by simpa [hindex] using Iter.yields_suffix ValueInst hlayout hdense hbits hvalid⟩

end milhouse.iter
