import Tree.ProgressiveList.Iter.Construction
import Tree.ProgressiveList.Encode.Metadata

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_list

/-- The direct-encoding loop is exactly the ordered fold of actual element
append calls. Each call receives its predecessor's returned buffer. Failure
and divergence propagate unchanged, with no codec or buffer-preservation law. -/
theorem ProgressiveList.ssz_append_fixed_loop_foldlM {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (cursor : ProgressiveListIter T U) (values : _root_.List T)
    (hyields : IteratorYields
      (ProgressiveListIter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst mapInst)
      cursor values) (buf : alloc.vec.Vec Std.U8) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0 ValueInst mapInst buf cursor =
      values.foldlM (fun buffer value => ValueInst.sszencodeEncodeInst.ssz_append value buffer) buf := by
  induction hyields generalizing buf with
  | nil hnext =>
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0.body,
      hnext, bind_tc_ok, _root_.List.foldlM_nil, Pure.pure]
  | @cons cursor rest value values hnext hyields ih =>
    rw [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0, loop]
    simp! only [ProgressiveList.Insts.SszEncodeEncode.ssz_append_loop0.body,
      hnext, bind_tc_ok, _root_.List.foldlM_cons]
    cases ValueInst.sszencodeEncodeInst.ssz_append value buf with
    | fail error => simp
    | div => simp
    | ok appended =>
      simp only [bind_tc_ok]
      exact ih appended

/-- Fixed-element encoding preserves the actual reservation checks and then
folds element append calls over the represented sequence. No relationship
between declared width and payload size, append law, or byte bound is assumed. -/
theorem ProgressiveList.ssz_append_fixed_calls {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (buf : alloc.vec.Vec Std.U8) :
    ProgressiveList.Insts.SszEncodeEncode.ssz_append ValueInst mapInst self buf = (do
      let count ← ProgressiveList.len ValueInst mapInst self
      let reservedLength ← width * count
      let reserved ← alloc.vec.Vec.reserve Global buf reservedLength
      contents.foldlM (fun buffer value => ValueInst.sszencodeEncodeInst.ssz_append value buffer)
        reserved) := by
  obtain ⟨cursor, hiter, _, _, hyields⟩ :=
    ProgressiveList.iter_spec ValueInst mapInst hlayout self contents hrep hdense hfits
  simp only [ProgressiveList.Insts.SszEncodeEncode.ssz_append, hfixed, hwidth,
    bind_tc_ok, ↓reduceIte, hiter]
  simp_rw [ProgressiveList.ssz_append_fixed_loop_foldlM ValueInst mapInst cursor contents hyields]

/-- The owning wrapper has the same exact call behavior from an empty buffer,
including reservation or element-call failure and divergence. -/
theorem ProgressiveList.as_ssz_bytes_fixed_calls {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0) :
    ProgressiveList.Insts.SszEncodeEncode.as_ssz_bytes ValueInst mapInst self = (do
      let count ← ProgressiveList.len ValueInst mapInst self
      let reservedLength ← width * count
      let reserved ← alloc.vec.Vec.reserve Global (alloc.vec.Vec.new Std.U8) reservedLength
      contents.foldlM (fun buffer value => ValueInst.sszencodeEncodeInst.ssz_append value buffer)
        reserved) := by
  rw [ProgressiveList.as_ssz_bytes_eq_append]
  exact ProgressiveList.ssz_append_fixed_calls ValueInst mapInst hfixed width hwidth hlayout
    self contents hrep hdense hfits (alloc.vec.Vec.new Std.U8)

end milhouse.progressive_list
