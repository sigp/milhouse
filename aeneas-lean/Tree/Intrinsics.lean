import Aeneas

open Aeneas Aeneas.Std Result

/-! Foundations for compiler-inserted operations in the source comparison
suites. Rust's `assume(true)` has no runtime effect; `assume(false)` is undefined
behavior, represented by Aeneas's `undef` failure. The Option residual proof
only reaches the true case, since `Option<Infallible>` can only be `None`.
These definitions do not replace an extracted Rust method. -/

@[rust_fun "core::intrinsics::assume"]
def core.intrinsics.assume (condition : Bool) : Result Unit :=
  if condition then ok () else fail .undef

/-- The only inhabited variant has logical discriminant zero. This instance
does not assert a memory layout for arbitrary options or references. -/
instance optionInfallibleDiscriminant :
    Discriminant (Option core.convert.Infallible) Std.Isize where
  read_discriminant _ := 0#isize
