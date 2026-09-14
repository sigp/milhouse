import Tree.Arbitrary.Models

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.arbitrary

theorem nextControl_empty (input : _root_.arbitrary.unstructured.Unstructured)
    (hempty : input.val = []) : nextControl input = (false, input) := by
  unfold nextControl
  split <;> simp_all

/-- Every nonempty control read consumes exactly one byte, including an even
byte that stops collection. No claim is made about element consumption. -/
theorem nextControl_cons (input rest : _root_.arbitrary.unstructured.Unstructured)
    (byte : Std.U8) (hinput : input.val = byte :: rest.val) :
    nextControl input = (decide (byte.val % 2 = 1), rest) := by
  unfold nextControl
  split <;> simp_all

/-- A finite successful generator trace records only actual control reads and
element calls. An element may consume, retain, or replace the input. -/
inductive Generates {T : Type} (inst : Arbitrary T) :
    _root_.arbitrary.unstructured.Unstructured → _root_.List T →
      _root_.arbitrary.unstructured.Unstructured → Prop
  | stop {input after} (hcontrol : nextControl input = (false, after)) :
      Generates inst input [] after
  | cons {input remaining next after value values}
      (hcontrol : nextControl input = (true, remaining))
      (hvalue : inst.arbitrary remaining = ok (.Ok value, next))
      (htail : Generates inst next values after) : Generates inst input (value :: values) after

/-- The first rejected element, following the recorded successful prefix.
Later control bytes and element calls are intentionally absent from the trace. -/
inductive Rejects {T : Type} (inst : Arbitrary T) :
    _root_.arbitrary.unstructured.Unstructured → _root_.List T → error.Error →
      _root_.arbitrary.unstructured.Unstructured → Prop
  | error {input remaining after error}
      (hcontrol : nextControl input = (true, remaining))
      (hvalue : inst.arbitrary remaining = ok (.Err error, after)) :
      Rejects inst input [] error after
  | cons {input remaining next after value values error}
      (hcontrol : nextControl input = (true, remaining))
      (hvalue : inst.arbitrary remaining = ok (.Ok value, next))
      (htail : Rejects inst next values error after) :
      Rejects inst input (value :: values) error after

/-- Collection terminates along every finite successful trace, with exact
accumulated values and final input. The final vector bound supplies each push. -/
theorem vector_loop_of_generates {T : Type} (inst : Arbitrary T)
    {input after : _root_.arbitrary.unstructured.Unstructured} {values : _root_.List T}
    (htrace : Generates inst input values after) (accumulator : alloc.vec.Vec T)
    (hbound : accumulator.val.length + values.length ≤ Std.Usize.max) :
    ∃ output, loop (vectorLoopBody inst) (accumulator, input) = ok (.Ok output, after) ∧
      output.val = accumulator.val ++ values := by
  induction htrace generalizing accumulator with
  | stop hcontrol =>
    refine ⟨accumulator, ?_, by simp⟩
    rw [loop]
    simp [vectorLoopBody, hcontrol]
  | @cons input remaining next after value values hcontrol hvalue htail ih =>
    have hroom : accumulator.val.length < Std.Usize.max := by
      simp only [_root_.List.length_cons] at hbound
      omega
    obtain ⟨pushed, hpush, hpushed⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec accumulator value hroom)
    have htailBound : pushed.val.length + values.length ≤ Std.Usize.max := by
      rw [hpushed]
      simp only [_root_.List.length_append, _root_.List.length_cons,
        _root_.List.length_nil] at hbound ⊢
      omega
    obtain ⟨output, hloop, houtput⟩ := ih pushed htailBound
    refine ⟨output, ?_, ?_⟩
    · rw [loop]
      simpa! only [vectorLoopBody, hcontrol, hvalue, hpush, bind_tc_ok, ↓reduceIte] using hloop
    · simpa only [hpushed, _root_.List.append_assoc, _root_.List.singleton_append] using houtput

/-- The concrete external Vec generator returns the entire traced sequence.
The vector itself supplies the capacity bound; no element-size or byte-length
law, successful collection call, or artificial fuel is assumed. -/
theorem vector_of_generates {T : Type} (inst : Arbitrary T)
    {input after : _root_.arbitrary.unstructured.Unstructured} (values : alloc.vec.Vec T)
    (htrace : Generates inst input values.val after) :
    vector inst input = ok (.Ok values, after) := by
  obtain ⟨output, hloop, houtput⟩ := vector_loop_of_generates inst htrace (alloc.vec.Vec.new T)
    (by simpa [alloc.vec.Vec.new] using values.property)
  have heq : output = values := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.new] using houtput)
  simpa only [vector, heq] using hloop

/-- Collection stops at the first error, after pushing the successful prefix,
and preserves the element generator's final input state exactly. -/
theorem vector_loop_of_rejects {T : Type} (inst : Arbitrary T)
    {input after : _root_.arbitrary.unstructured.Unstructured} {values : _root_.List T}
    {error : error.Error} (htrace : Rejects inst input values error after)
    (accumulator : alloc.vec.Vec T)
    (hbound : accumulator.val.length + values.length ≤ Std.Usize.max) :
    loop (vectorLoopBody inst) (accumulator, input) = ok (.Err error, after) := by
  induction htrace generalizing accumulator with
  | error hcontrol hvalue =>
    rw [loop]
    simp [vectorLoopBody, hcontrol, hvalue]
  | @cons input remaining next after value values error hcontrol hvalue htail ih =>
    have hroom : accumulator.val.length < Std.Usize.max := by
      simp only [_root_.List.length_cons] at hbound
      omega
    obtain ⟨pushed, hpush, hpushed⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec accumulator value hroom)
    have htailBound : pushed.val.length + values.length ≤ Std.Usize.max := by
      rw [hpushed]
      simp only [_root_.List.length_append, _root_.List.length_cons,
        _root_.List.length_nil] at hbound ⊢
      omega
    rw [loop]
    simpa! only [vectorLoopBody, hcontrol, hvalue, hpush, bind_tc_ok, ↓reduceIte]
      using ih pushed htailBound

theorem vector_of_rejects {T : Type} (inst : Arbitrary T)
    {input after : _root_.arbitrary.unstructured.Unstructured} (values : alloc.vec.Vec T)
    {error : error.Error} (htrace : Rejects inst input values.val error after) :
    vector inst input = ok (.Err error, after) :=
  vector_loop_of_rejects inst htrace (alloc.vec.Vec.new T)
    (by simpa [alloc.vec.Vec.new] using values.property)

end milhouse.arbitrary
