import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

/-- The successful element prefix consumed by a streaming SSZ cursor, ending
at exhaustion or the first boundary/element error. Calls after that stopping
point are deliberately unconstrained. This relation concerns cursor/decoder
calls only, independently of list construction. -/
inductive SszItems.Decodes {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError)) :
    SszItems → _root_.List T → Option ssz.decode.DecodeError → Prop where
  | exhausted {items rest}
      (hnext : SszItems.next items = ok (none, rest)) :
      Decodes decode items [] none
  | boundary_error {items rest error}
      (hnext : SszItems.next items = ok (some (core.result.Result.Err error), rest)) :
      Decodes decode items [] (some error)
  | element_error {items rest bytes error}
      (hnext : SszItems.next items = ok (some (core.result.Result.Ok bytes), rest))
      (hdecode : decode bytes = ok (core.result.Result.Err error)) :
      Decodes decode items [] (some error)
  | cons {items rest bytes value values error}
      (hnext : SszItems.next items = ok (some (core.result.Result.Ok bytes), rest))
      (hdecode : decode bytes = ok (core.result.Result.Ok value))
      (htail : Decodes decode rest values error) :
      Decodes decode items (value :: values) error

end milhouse.ssz_items
