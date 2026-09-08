import Tree.Types

open Aeneas Aeneas.Std Result
open milhouse

/-! Concrete external operations reached by the SSZ decoder. -/

@[rust_fun "core::hint::must_use"]
def core.hint.must_use {T : Type} (value : T) : Result T := ok value

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (value : core.result.Result T E) (f : O) :
    Result (core.result.Result T F) := do
  match value with
  | .Ok x => ok (.Ok x)
  | .Err e =>
    let e ← inst.call_once f e
    ok (.Err e)

/-- The public offset reader consumes the first four little-endian bytes and
ignores the suffix. A short input returns its actual length in the prefix error.
All four-byte values fit usize on both supported pointer widths. -/
@[rust_fun "ssz::decode::read_offset"]
def ssz.decode.read_offset (bytes : Slice Std.U8) :
    Result (core.result.Result Std.Usize milhouse.ssz.decode.DecodeError) :=
  match bytes.val with
  | a :: b :: c :: d :: _ =>
    ok (.Ok (UScalar.cast .Usize (core.num.U32.from_le_bytes
      (Array.make 4#usize [a, b, c, d]))))
  | _ => ok (.Err (.InvalidLengthPrefix bytes.len 4#usize))
