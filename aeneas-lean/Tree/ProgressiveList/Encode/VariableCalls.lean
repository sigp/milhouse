import Tree.ProgressiveList.Iter.Construction
import Tree.ProgressiveList.Encode.Metadata

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree
open _root_.ssz.encode

namespace milhouse.progressive_list

/-- The variable-encoding loop is exactly the ordered fold of encoder append
calls over the actual iterator sequence. Returned encoder states and borrowed
continuations are threaded in their actual order; failure and divergence
propagate unchanged. No metadata, codec, offset, or buffer law is assumed. -/
theorem ProgressiveList.ssz_append_variable_loop_foldlM {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (cursor : ProgressiveListIter T U) (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst)
      cursor values) (encoder : SszEncoder) (back : SszEncoder → SszEncoder) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1 ValueInst mapInst back encoder cursor =
      values.foldlM (fun (current, release) value => do
        let (next, appendBack) ← SszEncoder.append ValueInst.sszencodeEncodeInst current value
        ok (next, fun replacement => release (appendBack replacement))) (encoder, back) := by
  induction hyields generalizing encoder back with
  | nil hnext =>
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1.body,
      hnext, bind_tc_ok, _root_.List.foldlM_nil, Pure.pure]
  | @cons cursor rest value values hnext hyields ih =>
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop1.body,
      hnext, bind_tc_ok, _root_.List.foldlM_cons]
    cases SszEncoder.append ValueInst.sszencodeEncodeInst encoder value with
    | fail error => simp
    | div => simp
    | ok appended =>
      rcases appended with ⟨next, appendBack⟩
      simp only [bind_tc_ok]
      exact ih next (fun replacement => back (appendBack replacement))

/-- Public variable encoding performs its actual reservation, folds append
calls over the represented sequence, and finalizes through the actual borrowed
continuations. No element codec law or byte/offset bound is imposed. -/
theorem ProgressiveList.ssz_append_variable_calls {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hvariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (buf : alloc.vec.Vec Std.U8) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_append ValueInst mapInst self buf = (do
      let count ← ProgressiveList.len ValueInst mapInst self
      let fixedLength ← count * 4#usize
      let (encoder, containerBack) ← SszEncoder.container buf fixedLength
      let (encoded, release) ← contents.foldlM (fun (current, release) value => do
        let (next, appendBack) ← SszEncoder.append ValueInst.sszencodeEncodeInst current value
        ok (next, fun replacement => release (appendBack replacement))) (encoder, id)
      let (output, finalizeBack, finalizeBack1) ← SszEncoder.finalize encoded
      ok (containerBack (release (finalizeBack1 (finalizeBack output))))) := by
  obtain ⟨cursor, hiter, _, _, hyields⟩ :=
    ProgressiveList.iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  simp only [ProgressiveList.Insts.SszEncodeEncode.ssz_append, hvariable,
    bind_tc_ok, Bool.false_eq_true, ↓reduceIte, ssz.BYTES_PER_LENGTH_OFFSET, hiter]
  simp_rw [ProgressiveList.ssz_append_variable_loop_foldlM ValueInst mapInst cursor contents hyields]
  rfl

/-- Owning variable encoding has the same exact call behavior from an empty
destination, including reservation, append, or finalization failure/divergence. -/
theorem ProgressiveList.as_ssz_bytes_variable_calls {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hvariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ProgressiveList.Insts.SszEncodeEncode.as_ssz_bytes ValueInst mapInst self = (do
      let count ← ProgressiveList.len ValueInst mapInst self
      let fixedLength ← count * 4#usize
      let (encoder, containerBack) ← SszEncoder.container (alloc.vec.Vec.new Std.U8) fixedLength
      let (encoded, release) ← contents.foldlM (fun (current, release) value => do
        let (next, appendBack) ← SszEncoder.append ValueInst.sszencodeEncodeInst current value
        ok (next, fun replacement => release (appendBack replacement))) (encoder, id)
      let (output, finalizeBack, finalizeBack1) ← SszEncoder.finalize encoded
      ok (containerBack (release (finalizeBack1 (finalizeBack output))))) := by
  rw [ProgressiveList.as_ssz_bytes_eq_append]
  exact ProgressiveList.ssz_append_variable_calls ValueInst mapInst hvariable hlayout
    self contents hrep hdense hfits (alloc.vec.Vec.new Std.U8)

end milhouse.progressive_list
