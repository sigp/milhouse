import Tree.Arbitrary.Generation

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.arbitrary

/-- Successful collection has a finite trace of precisely the element calls
that produced the appended suffix. Divergence and failures need no premises. -/
theorem vector_loop_success_trace {T : Type} (inst : Arbitrary T) :
    ∀ state (output : alloc.vec.Vec T) after,
      loop (vectorLoopBody inst) state = ok (.Ok output, after) →
      ∃ values, Generates inst state.2 values after ∧ output.val = state.1.val ++ values := by
  apply loop.fixpoint_induct (vectorLoopBody inst)
    (fun recur => ∀ state (output : alloc.vec.Vec T) after,
      recur state = ok (.Ok output, after) →
      ∃ values, Generates inst state.2 values after ∧ output.val = state.1.val ++ values)
  · apply Lean.Order.admissible_pi
    intro state
    apply Lean.Order.admissible_pi
    intro output
    apply Lean.Order.admissible_pi
    intro after
    apply Lean.Order.admissible_apply
      (fun _ value => value = ok ((core.result.Result.Ok output :
        core.result.Result (alloc.vec.Vec T) error.Error), after) →
        ∃ values, Generates inst state.2 values after ∧ output.val = state.1.val ++ values)
    apply Lean.Order.admissible_flatOrder
    simp
  · intro recur ih state output after hresult
    rcases state with ⟨accumulator, input⟩
    rcases hcontrol : nextControl input with ⟨keepGoing, remaining⟩
    cases keepGoing with
    | false =>
      simp! only [vectorLoopBody, hcontrol, Bool.false_eq_true, ↓reduceIte] at hresult
      cases hresult
      exact ⟨[], .stop hcontrol, by simp⟩
    | true =>
      cases hvalue : inst.arbitrary remaining with
      | fail error => simp! [vectorLoopBody, hcontrol, hvalue] at hresult
      | div => simp! [vectorLoopBody, hcontrol, hvalue] at hresult
      | ok value =>
        rcases value with ⟨value, next⟩
        cases value with
        | Err error => simp! [vectorLoopBody, hcontrol, hvalue] at hresult
        | Ok value =>
          cases hpush : alloc.vec.Vec.push accumulator value with
          | fail error => simp! [vectorLoopBody, hcontrol, hvalue, hpush] at hresult
          | div => simp! [vectorLoopBody, hcontrol, hvalue, hpush] at hresult
          | ok pushed =>
            have hpushed : pushed.val = accumulator.val ++ [value] := by
              unfold alloc.vec.Vec.push at hpush
              dsimp only at hpush
              split at hpush
              · cases hpush
                simp
              · simp at hpush
            have hnext : recur (pushed, next) = ok (.Ok output, after) := by
              simpa! [vectorLoopBody, hcontrol, hvalue, hpush] using hresult
            obtain ⟨values, htrace, houtput⟩ := ih (pushed, next) output after hnext
            refine ⟨value :: values, .cons hcontrol hvalue htrace, ?_⟩
            simpa only [hpushed, _root_.List.append_assoc, _root_.List.singleton_append] using houtput

/-- The external Vec generator's successful results are exactly the finite
control/element traces. Thus a trace is a characterization of actual execution,
not an additional restriction on successful custom generators. -/
theorem vector_success_iff_generates {T : Type} (inst : Arbitrary T)
    (input after : _root_.arbitrary.unstructured.Unstructured) (values : alloc.vec.Vec T) :
    vector inst input = ok (.Ok values, after) ↔ Generates inst input values.val after := by
  constructor
  · intro hresult
    obtain ⟨generated, htrace, heq⟩ :=
      vector_loop_success_trace inst (alloc.vec.Vec.new T, input) values after hresult
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, _root_.List.nil_append] at heq
    simpa only [heq] using htrace
  · exact vector_of_generates inst values

end milhouse.arbitrary
