import Tree.ProgressiveList.Decode.VariableTotal
import Tree.ProgressiveList.Encode.Owning

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree
open _root_.ssz.encode

namespace milhouse.progressive_list

/-- Actual variable-element SSZ encoding followed by public decoding preserves
the complete merged sequence and every indexed read, with valid rebuilt backing
and no pending updates. Empty payloads are supported. The offset table supplies
all builder capacity bounds; only emitted offsets need to fit SSZ's 32 bits. -/
theorem ProgressiveList.ssz_roundtrip_variable {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) {factor : Option Std.Usize}
    {packingDepth : Std.Usize} (hlayout : PackingLayout ValueInst factor packingDepth)
    (hbacking : self.BackingValid factor)
    (hencodeVariable : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok false)
    (hdecodeVariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (encode : T → _root_.List Std.U8)
    (happend : ∀ value ∈ contents, ∀ buffer : alloc.vec.Vec Std.U8,
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hdecodeElement : ∀ value ∈ contents, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    (hbytes : 4 * contents.length + (contents.flatMap encode).length ≤ Std.Usize.max)
    (hoffsets : OffsetsFit encode (4 * contents.length) contents)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ bytes restored,
      ProgressiveList.Insts.SszEncodeEncode.as_ssz_bytes ValueInst mapInst self = ok bytes ∧
      ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes.deref =
        ok (core.result.Result.Ok restored) ∧ restored.Represents ValueInst mapInst contents ∧
      restored.BackingValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst restored = ok false ∧
      ∀ index, ProgressiveList.get ValueInst mapInst restored index =
        ProgressiveList.get ValueInst mapInst self index := by
  obtain ⟨bytes, hencode, hencoded⟩ := ProgressiveList.as_ssz_bytes_variable_spec ValueInst mapInst
    hencodeVariable hlayout self contents hrep hbacking.1 hbacking.2 encode happend hbytes hoffsets
  obtain ⟨restored, hdecode, hrestored, hbackingRestored, hpending⟩ :=
    ProgressiveList.from_ssz_bytes_variable_total_spec ValueInst mapInst bytes.deref contents encode
      hdecodeVariable hencoded hoffsets hdecodeElement hlayout updates hdefault hget hmax hempty
  refine ⟨bytes, restored, hencode, hdecode, hrestored, hbackingRestored, hpending, ?_⟩
  intro index
  rw [hrestored.2 index, hrep.2 index]

end milhouse.progressive_list
