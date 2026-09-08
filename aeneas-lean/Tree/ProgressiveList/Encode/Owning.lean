import Tree.ProgressiveList.Encode.Fixed
import Tree.ProgressiveList.Encode.Variable
import Tree.ProgressiveList.Encode.Metadata

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree
open _root_.ssz.encode

namespace milhouse.progressive_list

/-- Owning SSZ serialization returns exactly the fixed-element merged payload,
    using the proved append method and an initially empty output vector. -/
theorem ProgressiveList.as_ssz_bytes_fixed_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hfixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (width : Std.Usize) (hwidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (encode : T → _root_.List Std.U8)
    (hwidths : ∀ value ∈ contents, (encode value).length = width.val)
    (happend : ∀ value ∈ contents, ∀ buffer : alloc.vec.Vec Std.U8,
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hbound : width.val * contents.length ≤ Std.Usize.max) :
    ∃ output, ProgressiveList.Insts.SszEncodeEncode.as_ssz_bytes ValueInst mapInst self = ok output ∧
      output.val = contents.flatMap encode := by
  simpa only [ProgressiveList.as_ssz_bytes_eq_append, alloc.vec.Vec.new,
    _root_.List.nil_append] using ProgressiveList.ssz_append_fixed_spec ValueInst mapInst
      hfixed width hwidth hlayout self contents hrep hdense hfits encode (alloc.vec.Vec.new Std.U8)
      hwidths happend (by simpa using hbound)

/-- Owning variable-element serialization returns the exact SSZ offset table
    followed by all represented payloads, including pending values. -/
theorem ProgressiveList.as_ssz_bytes_variable_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hvariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hdense : self.tree.Dense factor 0 self.length.val) (hfits : self.tree.Fits factor 0)
    (encode : T → _root_.List Std.U8)
    (happend : ∀ value ∈ contents, ∀ buffer : alloc.vec.Vec Std.U8,
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hbound : 4 * contents.length + (contents.flatMap encode).length ≤ Std.Usize.max)
    (hoffsets : OffsetsFit encode (4 * contents.length) contents) :
    ∃ output, ProgressiveList.Insts.SszEncodeEncode.as_ssz_bytes ValueInst mapInst self = ok output ∧
      output.val = variableEncoding encode contents := by
  simpa only [ProgressiveList.as_ssz_bytes_eq_append, alloc.vec.Vec.new,
    _root_.List.nil_append] using ProgressiveList.ssz_append_variable_spec ValueInst mapInst
      hvariable hlayout self contents hrep hdense hfits encode (alloc.vec.Vec.new Std.U8)
      happend (by simpa using hbound) hoffsets

end milhouse.progressive_list
