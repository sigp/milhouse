import Aeneas

open Aeneas Aeneas.Std Result

/-! Local foundations for the September standard-library power algorithms.
The compiler selector is universally quantified. Each checked-power call
queries its base type at most once and U32 at most once; these outcomes are
independent. The source audit checks the complete caller before adding this
parameter and never substitutes a selected algorithm for the source body.

The numeric functions model integer logarithm, a checked shift, and the
power-of-two predicate. They are additional explicit source-comparison
boundaries, not claimed extractions of those primitive implementations. -/

class milhouse.compiler.StaticKnown where
  answer : {T : Type} → core.marker.Copy T → T → Bool

@[rust_fun "core::intrinsics::is_val_statically_known"]
def core.intrinsics.is_val_statically_known {T : Type}
    [milhouse.compiler.StaticKnown] (copy : core.marker.Copy T) (value : T) : Result Bool :=
  ok (milhouse.compiler.StaticKnown.answer copy value)

def milhouse.numeric.ilog2 {ty : UScalarTy} (value : UScalar ty) : Result Std.U32 :=
  if value.val = 0 then fail .panic else UScalar.tryMk .U32 value.val.log2

def milhouse.numeric.checked_shl {ty : UScalarTy} (value : UScalar ty)
    (shift : Std.U32) : Result (Option (UScalar ty)) :=
  if shift.val < ty.numBits then
    ok (some ⟨BitVec.ofNat ty.numBits (value.val * 2 ^ shift.val)⟩)
  else ok none

@[rust_fun "core::num::{u128}::ilog2"]
def core.num.U128.ilog2 := @milhouse.numeric.ilog2 .U128

@[rust_fun "core::num::{u128}::checked_shl"]
def core.num.U128.checked_shl := @milhouse.numeric.checked_shl .U128

@[rust_fun "core::num::{u128}::is_power_of_two"]
def core.num.U128.is_power_of_two (value : Std.U128) : Result Bool :=
  ok value.val.isPowerOfTwo
