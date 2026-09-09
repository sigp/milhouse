import Tree.Types

open Aeneas Aeneas.Std Result ControlFlow
open milhouse

namespace milhouse.arbitrary

/-- Pinned arbitrary 1.4.1 collection control: `ArbitraryIter::next` calls
`bool::arbitrary`, whose one-byte `fill_buffer` reads a byte or supplies zero
at exhaustion, then tests its low bit. An even control byte is consumed too.
The element generator is not called when this control value is false. -/
def nextControl (input : _root_.arbitrary.unstructured.Unstructured) : Bool × _root_.arbitrary.unstructured.Unstructured :=
  match h : input.val with
  | [] => (false, input)
  | byte :: rest =>
    (decide (byte.val % 2 = 1), ⟨rest, by
      have hbound := input.property
      rw [h] at hbound
      simp only [_root_.List.length_cons] at hbound
      omega⟩)

/-- One step of arbitrary 1.4.1's `Vec::arbitrary` collection. Rust's
`Result::from_iter` stops at the first element error, retaining the consumed
input state. No later control byte or element is visited after that error.
Vector allocation capacity is unobservable in the existing Vec model. -/
def vectorLoopBody {T : Type} (inst : Arbitrary T)
    (state : alloc.vec.Vec T × _root_.arbitrary.unstructured.Unstructured) :
    Result (ControlFlow (alloc.vec.Vec T × _root_.arbitrary.unstructured.Unstructured)
      (core.result.Result (alloc.vec.Vec T) error.Error × _root_.arbitrary.unstructured.Unstructured)) := do
  let (values, input) := state
  let (keepGoing, remaining) := nextControl input
  if keepGoing then
    let (value, after) ← inst.arbitrary remaining
    match value with
    | .Ok value =>
      let values ← alloc.vec.Vec.push values value
      ok (.cont (values, after))
    | .Err error => ok (.done (.Err error, after))
  else ok (.done (.Ok values, remaining))

/-- The full external vector generator, including divergence or failure of
custom element generators. The loop has no artificial fuel or input-length
termination bound: custom generators may replace their Unstructured input. -/
def vector {T : Type} (inst : Arbitrary T) (input : _root_.arbitrary.unstructured.Unstructured) :
    Result (core.result.Result (alloc.vec.Vec T) error.Error × _root_.arbitrary.unstructured.Unstructured) :=
  loop (vectorLoopBody inst) (alloc.vec.Vec.new T, input)

/-- Pinned trait default: run the ordinary generator on the owned input and
discard its final state. It does not call the element's take-rest generator. -/
@[trait_default, rust_fun "arbitrary::Arbitrary::arbitrary_take_rest"]
def Arbitrary.arbitrary_take_rest.default {Self : Type} (inst : Arbitrary Self)
    (input : _root_.arbitrary.unstructured.Unstructured) : Result (core.result.Result Self error.Error) := do
  let (result, _) ← inst.arbitrary input
  ok result

/-- Pinned trait default, independent of element behavior and depth. -/
@[trait_default, rust_fun "arbitrary::Arbitrary::size_hint"]
def Arbitrary.size_hint.default {Self : Type} (_inst : Arbitrary Self)
    (_depth : Std.Usize) : Result (Std.Usize × Option Std.Usize) := ok (0#usize, none)

/-- Pinned trait default delegates to the instance's actual size_hint. -/
@[trait_default, rust_fun "arbitrary::Arbitrary::try_size_hint"]
def Arbitrary.try_size_hint.default {Self : Type} (inst : Arbitrary Self)
    (depth : Std.Usize) :
    Result (core.result.Result (Std.Usize × Option Std.Usize) _root_.arbitrary.MaxRecursionReached) := do
  let hint ← inst.size_hint depth
  ok (.Ok hint)

end milhouse.arbitrary

namespace milhouse

/-- Pinned external Vec generator, implemented by the faithful control-byte
and element loop above. The actual ProgressiveList method remains extracted. -/
@[rust_fun "arbitrary::foreign::alloc::vec::{arbitrary::Arbitrary<'a, alloc::vec::Vec<@A>>}::arbitrary"]
def alloc.vec.Vec.Insts.ArbitraryArbitrary.arbitrary {A : Type}
    (inst : arbitrary.Arbitrary A) (input : _root_.arbitrary.unstructured.Unstructured) :
    Result (core.result.Result (alloc.vec.Vec A) arbitrary.error.Error ×
      _root_.arbitrary.unstructured.Unstructured) := arbitrary.vector inst input

end milhouse
