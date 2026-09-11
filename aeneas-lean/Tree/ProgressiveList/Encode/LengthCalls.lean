import Tree.ProgressiveList.Iter.Construction

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_list

/-- Size accumulation follows the actual element calls and checked additions
in order. A failing/diverging element call or overflowing addition prevents
later calls; no size law or arithmetic bound is assumed. -/
theorem ProgressiveList.ssz_bytes_len_loop_foldlM {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (cursor : ProgressiveListIter T U) (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst)
      cursor values) (accumulator : Std.Usize) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop
      ValueInst mapInst cursor accumulator =
      values.foldlM (fun (total : Std.Usize) value => do
        let size ← ValueInst.sszencodeEncodeInst.ssz_bytes_len value
        total + size) accumulator := by
  induction hyields generalizing accumulator with
  | nil hnext =>
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop.body,
      hnext, bind_tc_ok, _root_.List.foldlM_nil, Pure.pure]
  | @cons cursor rest value values hnext hyields ih =>
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len_loop.body,
      hnext, bind_tc_ok, _root_.List.foldlM_cons]
    cases ValueInst.sszencodeEncodeInst.ssz_bytes_len value with
    | fail error => simp
    | div => simp
    | ok size =>
      simp only [bind_tc_ok]
      cases accumulator + size with
      | fail error => simp
      | div => simp
      | ok next =>
        simp only [bind_tc_ok]
        exact ih next

/-- Variable-element size calculation folds actual size calls and checked
additions over the represented sequence before computing and adding the
offset-table size. Failure and divergence retain their actual order; no
element-size law or aggregate bound is imposed. -/
theorem ProgressiveList.ssz_bytes_len_variable_calls {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hvariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len ValueInst mapInst self = (do
      let payload ← contents.foldlM (fun (total : Std.Usize) value => do
        let size ← ValueInst.sszencodeEncodeInst.ssz_bytes_len value
        total + size) 0#usize
      let count ← ProgressiveList.len ValueInst mapInst self
      let offsets ← 4#usize * count
      payload + offsets) := by
  obtain ⟨cursor, hiter, _, _, hyields⟩ :=
    ProgressiveList.iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  simp only [ProgressiveList.Insts.SszEncodeEncode.ssz_bytes_len, hvariable,
    bind_tc_ok, Bool.false_eq_true, ↓reduceIte, hiter, ssz.BYTES_PER_LENGTH_OFFSET]
  rw [ProgressiveList.ssz_bytes_len_loop_foldlM ValueInst mapInst cursor contents hyields]

end milhouse.progressive_list
