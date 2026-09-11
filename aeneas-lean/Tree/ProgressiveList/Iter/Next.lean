import Tree.ProgressiveList.Iter.Cursor

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Exhausted list iterators return unchanged `none` without consulting either
    backing traversal or the pending map. This also covers past-end indices. -/
theorem ProgressiveListIter.next_exhausted {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveListIter T U) (hexhausted : self.length ≤ self.index) :
    ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst self =
      ok (none, self) := by
  simp only [ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next, if_pos hexhausted]

/-- A live list iterator returns the indexed merged value, advances once, and
    preserves its backing-suffix and overlay invariant. This includes pending
    replacements and extensions after the backing iterator is exhausted. -/
theorem ProgressiveListIter.next_live_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (backing contents : _root_.List T) (self : ProgressiveListIter T U)
    (hvalid : ProgressiveListIter.Valid ValueInst mapInst factor backing contents self)
    (hlive : self.index < self.length) :
    ∃ next,
      ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst self =
        ok (contents[self.index.val]?, next) ∧
      ProgressiveListIter.Valid ValueInst mapInst factor backing contents next ∧
      next.index.val = self.index.val + 1 ∧ next.length = self.length ∧ next.updates = self.updates := by
  obtain ⟨htree, hoverlay, hlength⟩ := hvalid
  obtain ⟨index, hindex, hindexVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := self.index) (y := 1#usize) (by scalar_tac))
  have hindexNat : index.val = self.index.val + 1 := by simpa using hindexVal
  obtain ⟨treeIter, hnext, htreeNext, _, _⟩ :=
    ProgressiveTreeIter.next_spec ValueInst hlayout self.tree_iter (backing.drop self.index.val) htree
  simp only [_root_.List.head?_drop] at hnext
  obtain ⟨pending, hget, hmerged⟩ := hoverlay self.index
  have hor : core.option.Option.or pending backing[self.index.val]? = ok contents[self.index.val]? := by
    cases pending <;> simpa [core.option.Option.or, Option.or] using
      congrArg (fun value : Option T => (ok value : Result (Option T))) hmerged
  refine ⟨{ self with tree_iter := treeIter, index }, ?_, ?_, hindexNat, rfl, rfl⟩
  · simp! only [ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      if_neg (not_le_of_gt hlive), hindex, hnext, hget, hor, bind_tc_ok]
  · refine ⟨?_, hoverlay, hlength⟩
    simpa only [_root_.List.tail_drop, hindexNat] using htreeNext

/-- A valid list cursor enumerates exactly the represented merged suffix and
    then returns `none`. No extra update-map law or iterator-output premise is
    required: the cursor's overlay is established from list representation. -/
theorem ProgressiveListIter.yields_suffix {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (backing contents : _root_.List T) (self : ProgressiveListIter T U)
    (hvalid : ProgressiveListIter.Valid ValueInst mapInst factor backing contents self) :
    IteratorYields (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst)
      self (contents.drop self.index.val) := by
  generalize hm : contents.length - self.index.val = remaining
  induction remaining using Nat.strong_induction_on generalizing self with
  | h remaining ih =>
    have hlength := @ProgressiveListIter.Valid.length_eq T U ValueInst mapInst factor backing contents self hvalid
    by_cases hlive : self.index < self.length
    · have hinside : self.index.val < contents.length := by scalar_tac
      obtain ⟨next, hnext, hnextValid, hindex, _, _⟩ :=
        ProgressiveListIter.next_live_spec ValueInst mapInst hlayout backing contents self hvalid hlive
      rw [_root_.List.drop_eq_getElem_cons hinside]
      refine .cons (rest := next) ?_ ?_
      · simpa only [_root_.List.getElem?_eq_getElem hinside] using hnext
      · have htail := ih (contents.length - next.index.val) (by omega) next hnextValid rfl
        simpa [hindex] using htail
    · have hbound : contents.length ≤ self.index.val := by scalar_tac
      rw [_root_.List.drop_eq_nil_of_le hbound]
      exact .nil (ProgressiveListIter.next_exhausted ValueInst mapInst self (le_of_not_gt hlive))

end milhouse.progressive_list
