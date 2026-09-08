import Tree.ProgressiveList.Iter.Next

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The shared constructor installs the backing suffix at the requested index
    and the pending overlay derived from the list's representation. Clamping
    to the backing length preserves the suffix even when updates extend it. -/
theorem ProgressiveList.iter_from_unchecked_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ∃ cursor, ProgressiveList.iter_from_unchecked ValueInst mapInst self index = ok cursor ∧
      ProgressiveListIter.Valid ValueInst mapInst factor self.tree.elements contents cursor ∧
      cursor.index = index := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  obtain ⟨start, hmin, hminEq⟩ := WP.spec_imp_exists
    (core.cmp.Ord.min.trait_default_Usize.spec index self.length)
  have hstartVal : start.val = min index.val self.length.val := by
    rw [hminEq, core.cmp.impls.OrdUsize.min_val]
  obtain ⟨treeIter, hfrom, htree, _, _⟩ :=
    ProgressiveTreeIter.from_index_spec ValueInst hlayout self.tree start self.length hdense hfits
  refine ⟨{ tree_iter := treeIter, updates := self.updates, index, length }, ?_, ?_, rfl⟩
  · simp! only [ProgressiveList.iter_from_unchecked, ProgressiveList.backing_len,
      utils.Length.as_usize, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
      hmin, ProgressiveTree.iter_from, hfrom, hlen, bind_tc_ok]
  · refine ⟨?_, hrep.overlay ValueInst mapInst hlayout self contents hdense hfits, hlength⟩
    have hdrop : self.tree.elements.drop start.val = self.tree.elements.drop index.val := by
      rw [hstartVal, ← hdense.elements_length]
      exact _root_.List.drop_eq_drop_min.symm
    simpa only [hdrop] using htree

/-- Public `iter` succeeds and enumerates every represented value in order,
    including pending replacements and pending extension beyond the backing
    tree. Its cursor invariant follows from representation and backing density. -/
theorem ProgressiveList.iter_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ∃ cursor, ProgressiveList.iter ValueInst mapInst self = ok cursor ∧
      ProgressiveListIter.Valid ValueInst mapInst factor self.tree.elements contents cursor ∧
      cursor.index = 0#usize ∧
      IteratorYields (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst)
        cursor contents := by
  obtain ⟨cursor, hfrom, hvalid, hindex⟩ :=
    ProgressiveList.iter_from_unchecked_spec ValueInst mapInst hlayout self contents 0#usize hrep hdense hfits
  refine ⟨cursor, hfrom, hvalid, hindex, ?_⟩
  simpa [hindex] using ProgressiveListIter.yields_suffix ValueInst mapInst hlayout self.tree.elements contents cursor hvalid

/-- Public `iter_from` accepts every index up to and including the logical end
    and enumerates exactly the corresponding represented suffix. -/
theorem ProgressiveList.iter_from_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (hindex : index.val ≤ contents.length) :
    ∃ cursor, ProgressiveList.iter_from ValueInst mapInst self index = ok (core.result.Result.Ok cursor) ∧
      ProgressiveListIter.Valid ValueInst mapInst factor self.tree.elements contents cursor ∧
      cursor.index = index ∧
      IteratorYields (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst)
        cursor (contents.drop index.val) := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  obtain ⟨cursor, hfrom, hvalid, hcursorIndex⟩ :=
    ProgressiveList.iter_from_unchecked_spec ValueInst mapInst hlayout self contents index hrep hdense hfits
  refine ⟨cursor, ?_, hvalid, hcursorIndex, ?_⟩
  · have hinside : ¬ index > length := by scalar_tac
    simp only [ProgressiveList.iter_from, hlen, bind_tc_ok, if_neg hinside, hfrom]
  · simpa [hcursorIndex] using ProgressiveListIter.yields_suffix ValueInst mapInst hlayout self.tree.elements contents cursor hvalid

/-- Out-of-bounds public starts return the specified error and exact logical
    length. This branch needs no backing-tree or element-packing invariant. -/
theorem ProgressiveList.iter_from_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : contents.length < index.val) :
    ∃ length : Std.Usize, length.val = contents.length ∧
      ProgressiveList.iter_from ValueInst mapInst self index =
        ok (core.result.Result.Err (error.Error.OutOfBoundsIterFrom index length)) := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  refine ⟨length, hlength, ?_⟩
  have houtside : index > length := by scalar_tac
  simp only [ProgressiveList.iter_from, hlen, bind_tc_ok, if_pos houtside]

end milhouse.progressive_list
