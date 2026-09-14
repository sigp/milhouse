import Tree.Ssz.PayloadTrace

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

/-- A complete input decoding trace: empty input bypasses metadata; nonempty
input uses the actual fixed metadata or variable cursor initialization, then
exhausts the cursor without a boundary or element error. Each value retains
its own accepted payload. This relation contains no list-construction call. -/
inductive SszItems.DecodesBytes {T : Type} (decodeInst : ssz.decode.Decode T) :
    Slice Std.U8 → _root_.List (T × _root_.List Std.U8) → Prop
  | empty {bytes : Slice Std.U8} (hbytes : bytes.val = []) :
      DecodesBytes decodeInst bytes []
  | fixed {bytes : Slice Std.U8} {width : Std.Usize}
      {entries : _root_.List (T × _root_.List Std.U8)}
      (hnonempty : bytes.val ≠ [])
      (hfixed : decodeInst.is_ssz_fixed_len = ok true)
      (hwidth : decodeInst.ssz_fixed_len = ok width) (hnonzero : width ≠ 0#usize)
      (htrace : (SszItems.Fixed bytes width).Decodes
        (SszItems.recordPayload decodeInst.from_ssz_bytes) entries none) :
      DecodesBytes decodeInst bytes entries
  | variable {bytes : Slice Std.U8} {items : SszItems}
      {entries : _root_.List (T × _root_.List Std.U8)}
      (hnonempty : bytes.val ≠ [])
      (hvariable : decodeInst.is_ssz_fixed_len = ok false)
      (hitems : SszItems.variable bytes = ok (core.result.Result.Ok items))
      (htrace : items.Decodes (SszItems.recordPayload decodeInst.from_ssz_bytes) entries none) :
      DecodesBytes decodeInst bytes entries

end milhouse.ssz_items
