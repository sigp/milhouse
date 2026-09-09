import Tree.ProgressiveList.Decode.Entry
import Tree.ProgressiveList.Decode.Success
import Tree.Ssz.DecodedLength

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- A fixed-format cursor or element error is returned by the public decoder
after the actual builder finalizes its decoded prefix. Builder success and
termination follow from packing and representability, not from a premise
about the list decoder's result. -/
theorem ProgressiveList.from_ssz_bytes_fixed_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (width : Std.Usize) (values : _root_.List T)
    (error : ssz.decode.DecodeError) (hnonempty : bytes.val ≠ [])
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hpositive : 0 < width.val)
    (hitems : (ssz_items.SszItems.Fixed bytes width).Decodes
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes values (some error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  have hwidthNe : width ≠ 0#usize := by
    intro h
    subst width
    change 0 < 0 at hpositive
    omega
  obtain ⟨self, hdecode⟩ := ProgressiveList.decode_ssz_items_success ValueInst mapInst
    (.Fixed bytes width) values (some error) hitems hlayout hfits updates hdefault
  simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
    hnonempty, hfixed, hwidth, hwidthNe, hdecode, core.result.Result.map_err]

/-- After a valid first offset, the public variable decoder returns the first
cursor or element error. The offset table bounds the consumed prefix, supplying
every builder capacity bound even when later offsets or payloads are malformed. -/
theorem ProgressiveList.from_ssz_bytes_variable_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (first count : Std.Usize) (values : _root_.List T)
    (error : ssz.decode.DecodeError)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hread : _root_.ssz.decode.read_offset bytes = ok (core.result.Result.Ok first))
    (hfirst : first.val = 4 * count.val) (hcount : 0 < count.val)
    (hbound : first.val ≤ bytes.length)
    (hitems : (ssz_items.SszItems.Variable bytes first count 1#usize first).Decodes
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes values (some error))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err error) := by
  have hnonempty : bytes.val ≠ [] := by
    intro h
    simp only [Slice.length, h, _root_.List.length_nil] at hbound
    omega
  have hlength := ssz_items.SszItems.decodes_variable_length_le
    ValueInst.sszdecodeDecodeInst.from_ssz_bytes bytes first count 1#usize first values
    (some error) hitems
  have hfits : ProgressiveTree.LengthFits factor values.length :=
    ProgressiveTree.LengthFits.of_four_mul_le_max factor (by
      have hb := bytes.property
      change values.length ≤ count.val + 1 - 1 at hlength
      simp only [Slice.length] at hbound
      omega)
  have hinit := ssz_items.SszItems.variable_valid bytes first count hread hfirst hcount hbound
  obtain ⟨self, hdecode⟩ := ProgressiveList.decode_ssz_items_success ValueInst mapInst
    (.Variable bytes first count 1#usize first) values (some error) hitems hlayout hfits
    updates hdefault
  simp! [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, core.slice.Slice.is_empty,
    hnonempty, hvariable, hinit, core.result.Result.Insts.CoreOpsTry.branch, hdecode]

end milhouse.progressive_list
