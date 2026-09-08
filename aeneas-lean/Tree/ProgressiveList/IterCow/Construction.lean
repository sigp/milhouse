import Tree.ProgressiveList.IterCow.State
import Tree.ProgressiveList.Iter.Cursor

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- A CoW cursor starts at the correct materialized suffix and retains the
    represented pending overlay. The sequence length bounds live increments;
    it is derived from list representation, not assumed separately. -/
structure ProgressiveListIterCow.Valid {T U : Type} (ValueInst : Value T)
    (mapInst : update_map.UpdateMap U T) (factor : Option Std.Usize)
    (backing contents : _root_.List T) (self : ProgressiveListIterCow T U) : Prop where
  tree : ProgressiveTreeIter.Valid ValueInst factor self.tree_iter (backing.drop self.index.val)
  overlay : ProgressiveListIter.Overlay mapInst self.updates backing contents
  length_bound : contents.length ≤ Std.Usize.max

/-- The shared CoW constructor installs the exact backing suffix, preserves
    pending state, and returns a continuation that writes only that state back.
    No additional map or cloning law is required for construction. -/
theorem ProgressiveList.iter_cow_from_unchecked_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor) :
    ∃ cursor back,
      ProgressiveList.iter_cow_from_unchecked ValueInst mapInst self index = ok (cursor, back) ∧
      ProgressiveListIterCow.Valid ValueInst mapInst factor self.tree.elements contents cursor ∧
      cursor.index = index ∧ cursor.updates = self.updates ∧
      back = fun replacement => { self with updates := replacement.updates } := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  obtain ⟨start, hmin, hminEq⟩ := WP.spec_imp_exists
    (core.cmp.Ord.min.trait_default_Usize.spec index self.length)
  have hstartVal : start.val = min index.val self.length.val := by
    rw [hminEq, core.cmp.impls.OrdUsize.min_val]
  obtain ⟨treeIter, hfrom, htree, _, _⟩ :=
    ProgressiveTreeIter.from_index_spec ValueInst hlayout self.tree start self.length hbacking.1 hbacking.2
  refine ⟨{ tree_iter := treeIter, updates := self.updates, index },
    (fun replacement => { self with updates := replacement.updates }), ?_, ?_, rfl, rfl, rfl⟩
  · simp! only [ProgressiveList.iter_cow_from_unchecked, ProgressiveList.backing_len,
      utils.Length.as_usize, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
      hmin, ProgressiveTree.iter_from, hfrom, bind_tc_ok]
  · refine ⟨?_, hrep.overlay ValueInst mapInst hlayout self contents hbacking.1 hbacking.2, ?_⟩
    · have hdrop : self.tree.elements.drop start.val = self.tree.elements.drop index.val := by
        rw [hstartVal, ← hbacking.1.elements_length]
        exact _root_.List.drop_eq_drop_min.symm
      simpa only [hdrop] using htree
    · rw [← hlength]
      scalar_tac

/-- Public CoW iteration creates a valid cursor at zero and leaves the pending
    map untouched. Its continuation changes only the pending map. -/
theorem ProgressiveList.iter_cow_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor) :
    ∃ cursor back,
      ProgressiveList.iter_cow ValueInst mapInst self = ok (cursor, back) ∧
      ProgressiveListIterCow.Valid ValueInst mapInst factor self.tree.elements contents cursor ∧
      cursor.index = 0#usize ∧ cursor.updates = self.updates ∧
      back = fun replacement => { self with updates := replacement.updates } := by
  obtain ⟨cursor, back, hfrom, hvalid, hindex, hupdates, rfl⟩ :=
    ProgressiveList.iter_cow_from_unchecked_spec ValueInst mapInst hlayout self contents 0#usize hrep hbacking
  refine ⟨cursor, (fun replacement => { self with updates := replacement.updates }), ?_,
    hvalid, hindex, hupdates, rfl⟩
  simp! only [ProgressiveList.iter_cow, hfrom, bind_tc_ok]

/-- Every start up to and including the logical end succeeds with the correct
    CoW suffix cursor. Successful cursor write-back affects only pending state;
    replacing the returned result with an error restores the original list. -/
theorem ProgressiveList.iter_cow_from_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents)
    (hbacking : self.BackingValid factor) (hindex : index.val ≤ contents.length) :
    ∃ cursor back,
      ProgressiveList.iter_cow_from ValueInst mapInst self index = ok (core.result.Result.Ok cursor, back) ∧
      ProgressiveListIterCow.Valid ValueInst mapInst factor self.tree.elements contents cursor ∧
      cursor.index = index ∧ cursor.updates = self.updates ∧
      (∀ replacement, back (core.result.Result.Ok replacement) = { self with updates := replacement.updates }) ∧
      (∀ err, back (core.result.Result.Err err) = self) := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  obtain ⟨cursor, back, hfrom, hvalid, hcursorIndex, hupdates, rfl⟩ :=
    ProgressiveList.iter_cow_from_unchecked_spec ValueInst mapInst hlayout self contents index hrep hbacking
  let back := fun (result : core.result.Result (ProgressiveListIterCow T U) error.Error) => match result with
    | core.result.Result.Ok replacement => { self with updates := replacement.updates }
    | core.result.Result.Err _ => self
  refine ⟨cursor, back, ?_, hvalid, hcursorIndex, hupdates, fun _ => rfl, fun _ => rfl⟩
  have hinside : ¬ index > length := by scalar_tac
  simp! only [ProgressiveList.iter_cow_from, hlen, bind_tc_ok, if_neg hinside, hfrom, ok.injEq,
    Prod.mk.injEq, true_and]
  funext result
  cases result with
  | Err err => simp [back, hupdates]
  | Ok replacement => cases replacement; rfl

/-- Oversized CoW starts return the exact bounds error and preserve the entire
    list for every continuation input. No backing or packing invariant is needed. -/
theorem ProgressiveList.iter_cow_from_out_of_bounds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (index : Std.Usize)
    (hrep : self.Represents ValueInst mapInst contents) (hindex : contents.length < index.val) :
    ∃ length : Std.Usize, length.val = contents.length ∧
      ProgressiveList.iter_cow_from ValueInst mapInst self index =
        ok (core.result.Result.Err (error.Error.OutOfBoundsIterFrom index length), fun _ => self) := by
  obtain ⟨length, hlen, hlength⟩ := hrep.1
  refine ⟨length, hlength, ?_⟩
  have houtside : index > length := by scalar_tac
  simp only [ProgressiveList.iter_cow_from, hlen, bind_tc_ok, if_pos houtside]

end milhouse.progressive_list
