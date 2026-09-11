import Tree.Types

open Aeneas Aeneas.Std Result
open milhouse

/-! Concrete external models for ethereum_ssz 0.10.0 encoding. Allocations
    and capacity are erased as in Aeneas's Vec model; logical size overflow
    remains checked. The offset check follows the debug-assertion-enabled
    development profile used by extraction. -/

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::reserve"]
def alloc.vec.Vec.reserve {T : Type} (_A : Type) (self : alloc.vec.Vec T)
    (additional : Std.Usize) : Result (alloc.vec.Vec T) :=
  if self.val.length + additional.val ≤ Std.Usize.max then ok self else fail .panic

@[rust_const "ssz::BYTES_PER_LENGTH_OFFSET"]
def ssz.BYTES_PER_LENGTH_OFFSET : Result Std.Usize := ok 4#usize

namespace ssz.encode

/-- Copy bytes without element cloning; this is the byte-vector append used
    by the encoder's offset writes and finalization. -/
def append_bytes (buf : alloc.vec.Vec Std.U8) (bytes : _root_.List Std.U8) :
    Result (alloc.vec.Vec Std.U8) :=
  if h : buf.val.length + bytes.length ≤ Std.Usize.max then
    ok (alloc.vec.Vec.from (buf.val ++ bytes) (by simpa only [_root_.List.length_append] using h))
  else fail .panic

/-- SSZ's four little-endian offset bytes, including its development-profile
    assertion that the offset fits 32 bits. -/
def encode_length (length : Std.Usize) : Result (_root_.List Std.U8) :=
  if length.val ≤ Std.U32.max then
    ok (core.num.U32.to_le_bytes (UScalar.cast .U32 length)).val
  else fail .panic

@[rust_fun "ssz::encode::{ssz::encode::SszEncoder<'a>}::container"]
def SszEncoder.container (buf : alloc.vec.Vec Std.U8) (num_fixed_bytes : Std.Usize) :
    Result (SszEncoder × (SszEncoder → alloc.vec.Vec Std.U8)) := do
  let buf ← alloc.vec.Vec.reserve Global buf num_fixed_bytes
  ok (⟨num_fixed_bytes, buf, alloc.vec.Vec.new Std.U8⟩, fun encoder => encoder.buf)

@[rust_fun "ssz::encode::{ssz::encode::SszEncoder<'a>}::append"]
def SszEncoder.append {T : Type} (EncodeInst : milhouse.ssz.encode.Encode T) (self : SszEncoder) (item : T) :
    Result (SszEncoder × (SszEncoder → SszEncoder)) := do
  let fixed ← EncodeInst.is_ssz_fixed_len
  if fixed then
    let buf ← EncodeInst.ssz_append item self.buf
    ok ({ self with buf }, id)
  else
    let offset ← self.offset + self.variable_bytes.len
    let offset_bytes ← encode_length offset
    let buf ← append_bytes self.buf offset_bytes
    let variable_bytes ← EncodeInst.ssz_append item self.variable_bytes
    ok ({ self with buf, variable_bytes }, id)

@[rust_fun "ssz::encode::{ssz::encode::SszEncoder<'a>}::finalize"]
def SszEncoder.finalize (self : SszEncoder) :
    Result (alloc.vec.Vec Std.U8 × (alloc.vec.Vec Std.U8 → SszEncoder) ×
      (SszEncoder → SszEncoder)) := do
  let buf ← append_bytes self.buf self.variable_bytes.val
  ok (buf, fun replacement => { self with buf := replacement, variable_bytes := alloc.vec.Vec.new Std.U8 }, id)

end ssz.encode
