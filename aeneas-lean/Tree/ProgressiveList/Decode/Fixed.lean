import Tree.ProgressiveList.Decode.Backing
import Tree.ProgressiveList.Decode.Contents
import Tree.Ssz.FixedCursor

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_list

/-- A successful fixed-format decode materializes the encoded values in order,
records their exact length, and initializes the actual default update map.
The cursor and builder properties are derived internally; only the element
width and exact-payload decoder laws are required. Empty inputs are included. -/
theorem ProgressiveList.from_ssz_bytes_fixed_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (width : Std.Usize) (hpositive : 0 < width.val)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = values.flatMap encode)
    (hsize : ∀ value ∈ values, (encode value).length = width.val)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    self.tree.elements = values ∧ self.length.val = values.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  cases values with
  | nil =>
    rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes (by simpa using hbytes)] at hdecode
    rw [bind_eq_ok_iff] at hdecode
    obtain ⟨result, hempty, heq⟩ := hdecode
    simp only [ok.injEq, core.result.Result.Ok.injEq] at heq
    cases heq
    obtain ⟨htree, hlength, hdefault⟩ := ProgressiveList.empty_success_state ValueInst mapInst hempty
    exact ⟨by simp [htree, progressive_tree.ProgressiveTree.elements], by simp [hlength], hdefault⟩
  | cons value values =>
    have hnonempty : bytes.val ≠ [] := by
      intro hempty
      have hsize1 := hsize value (by simp)
      have hlen := congrArg _root_.List.length hbytes
      simp only [hempty, _root_.List.length_nil, _root_.List.flatMap_cons,
        _root_.List.length_append, hsize1] at hlen
      omega
    have hitems := ssz_items.SszItems.fixed_decodes_values
      ValueInst.sszdecodeDecodeInst.from_ssz_bytes encode width hpositive
      (value :: values) bytes hbytes hsize hdecodeElement
    have hbuild := ProgressiveList.from_ssz_bytes_fixed_success
      ValueInst mapInst bytes width hnonempty hfixed hwidth hdecode
    obtain ⟨helements, hlength, hdefault, _⟩ := ProgressiveList.decode_ssz_items_contents
      ValueInst mapInst (.Fixed bytes width) (value :: values) none hitems hbuild
    exact ⟨helements, hlength, hdefault⟩

/-- Complete sequence-level partial correctness for fixed-element SSZ
decoding: every indexed read agrees with the input values, the backing tree
is valid for traversal, and no updates are pending. No iterator-output,
builder-invariant, clone, or additional arithmetic premise is exposed. -/
theorem ProgressiveList.from_ssz_bytes_fixed_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (values : _root_.List T) (encode : T → _root_.List Std.U8)
    (width : Std.Usize) (hpositive : 0 < width.val)
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (hbytes : bytes.val = values.flatMap encode)
    (hsize : ∀ value ∈ values, (encode value).length = width.val)
    (hdecodeElement : ∀ value ∈ values, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hdefault : ∀ updates, mapInst.coredefaultDefaultInst.default = ok updates →
      (∀ index, mapInst.get updates index = ok none) ∧
        mapInst.max_index updates = ok none ∧ mapInst.is_empty updates = ok true)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    self.Represents ValueInst mapInst values ∧ self.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨helements, _, hmap⟩ := ProgressiveList.from_ssz_bytes_fixed_contents
    ValueInst mapInst bytes values encode width hpositive hfixed hwidth hbytes hsize hdecodeElement hdecode
  obtain ⟨hbacking, _⟩ := ProgressiveList.from_ssz_bytes_backing ValueInst mapInst bytes hlayout hdecode
  obtain ⟨hget, hmax, hempty⟩ := hdefault self.updates hmap
  refine ⟨?_, hbacking, ProgressiveList.has_pending_updates_spec ValueInst mapInst self true hempty⟩
  rw [← helements]
  exact ProgressiveList.represents_of_dense_backing ValueInst mapInst hlayout self
    hbacking.1 hbacking.2 hget hmax

end milhouse.progressive_list
