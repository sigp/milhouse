import Tree.ProgressiveList.Decode.FixedTotal
import Tree.ProgressiveList.Encode.Owning

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The actual owning encoder and public fixed-element decoder both succeed
and preserve every indexed value, including pending replacements/extensions.
The reconstructed list has valid backing and no pending updates. Byte size
and occupied-layer bounds describe the two operations' representable domains;
all intermediate arithmetic and traversal conditions are derived internally.
Decoder metadata, positive width, and reconstruction capacity are needed only
for nonempty contents; encoder/traversal premises describe their actual calls. -/
theorem ProgressiveList.ssz_roundtrip_fixed {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T)
    (hrep : self.Represents ValueInst mapInst contents) {factor : Option Std.Usize}
    {packingDepth : Std.Usize} (hlayout : PackingLayout ValueInst factor packingDepth)
    (hbacking : self.BackingValid factor)
    (hfits : contents ≠ [] → ProgressiveTree.LengthFits factor contents.length)
    (width : Std.Usize) (hpositive : contents ≠ [] → 0 < width.val)
    (hencodeFixed : ValueInst.sszencodeEncodeInst.is_ssz_fixed_len = ok true)
    (hencodeWidth : ValueInst.sszencodeEncodeInst.ssz_fixed_len = ok width)
    (hdecodeFixed : contents ≠ [] → ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hdecodeWidth : contents ≠ [] → ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    (encode : T → _root_.List Std.U8)
    (hwidths : ∀ value ∈ contents, (encode value).length = width.val)
    (happend : ∀ value ∈ contents, ∀ buffer : alloc.vec.Vec Std.U8,
      buffer.val.length + (encode value).length ≤ Std.Usize.max →
      ∃ output, ValueInst.sszencodeEncodeInst.ssz_append value buffer = ok output ∧
        output.val = buffer.val ++ encode value)
    (hdecodeElement : ∀ value ∈ contents, ∀ part : Slice Std.U8,
      part.val = encode value → ValueInst.sszdecodeDecodeInst.from_ssz_bytes part =
        ok (core.result.Result.Ok value))
    (hbytes : width.val * contents.length ≤ Std.Usize.max)
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
  obtain ⟨bytes, hencode, hencoded⟩ := ProgressiveList.as_ssz_bytes_fixed_spec ValueInst mapInst
    hencodeFixed width hencodeWidth hlayout self contents hrep hbacking.1 hbacking.2
    encode hwidths happend hbytes
  obtain ⟨restored, hdecode, hrestored, hbackingRestored, hpending⟩ :=
    ProgressiveList.from_ssz_bytes_fixed_total_spec ValueInst mapInst bytes.deref contents encode width
      hpositive hdecodeFixed hdecodeWidth hencoded hwidths hdecodeElement (fun _ => hlayout) hfits
      updates hdefault hget hmax hempty
  refine ⟨bytes, restored, hencode, hdecode, hrestored, hbackingRestored, hpending, ?_⟩
  intro index
  rw [hrestored.2 index, hrep.2 index]

end milhouse.progressive_list
