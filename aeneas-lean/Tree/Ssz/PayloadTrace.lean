import Tree.Ssz.DecodedItems

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

/-- A proof-level annotation of the actual element decoder with the bytes it
consumed. This permits equal decoded values to have different input encodings. -/
def SszItems.recordPayload {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (bytes : Slice Std.U8) : Result (core.result.Result (T × _root_.List Std.U8)
      ssz.decode.DecodeError) := do
  let result ← decode bytes
  match result with
  | .Ok value => ok (.Ok (value, bytes.val))
  | .Err error => ok (.Err error)

theorem SszItems.recordPayload_ok_iff {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (bytes : Slice Std.U8) (entry : T × _root_.List Std.U8) :
    SszItems.recordPayload decode bytes = ok (core.result.Result.Ok entry) ↔
      decode bytes = ok (core.result.Result.Ok entry.1) ∧ bytes.val = entry.2 := by
  cases entry with
  | mk value payload =>
    cases h : decode bytes with
    | fail error => simp [SszItems.recordPayload, h]
    | div => simp [SszItems.recordPayload, h]
    | ok result => cases result <;> simp [SszItems.recordPayload, h]

theorem SszItems.recordPayload_error_iff {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (bytes : Slice Std.U8) (error : ssz.decode.DecodeError) :
    SszItems.recordPayload decode bytes = ok (core.result.Result.Err error) ↔
      decode bytes = ok (core.result.Result.Err error) := by
  cases h : decode bytes with
  | fail error => simp [SszItems.recordPayload, h]
  | div => simp [SszItems.recordPayload, h]
  | ok result => cases result <;> simp [SszItems.recordPayload, h]

/-- Erasing payload annotations recovers the exact original decoder trace,
including its stopping error. This needs no canonical-encoding or decoder
injectivity law. The cursor itself is unchanged. -/
theorem SszItems.Decodes.forget_payload {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (items : SszItems) (entries : _root_.List (T × _root_.List Std.U8))
    (error : Option ssz.decode.DecodeError)
    (htrace : items.Decodes (SszItems.recordPayload decode) entries error) :
    items.Decodes decode (entries.map Prod.fst) error := by
  induction htrace with
  | exhausted hnext => exact .exhausted hnext
  | boundary_error hnext => exact .boundary_error hnext
  | element_error hnext hdecode =>
    exact .element_error hnext ((SszItems.recordPayload_error_iff decode _ _).mp hdecode)
  | cons hnext hdecode htail ih =>
    exact .cons hnext ((SszItems.recordPayload_ok_iff decode _ _).mp hdecode).1 ih

end milhouse.ssz_items
