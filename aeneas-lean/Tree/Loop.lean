import Aeneas

open Aeneas Aeneas.Std Result

namespace milhouse

/-- An invariant of successful loop-body steps holds at every successful loop
    exit. This partial-correctness rule adds no termination or failure-freedom
    premise: divergence and failures cannot produce a successful result. -/
theorem loop_success_invariant {α β : Type}
    (body : α → Result (ControlFlow α β)) (inv : α → Prop) (post : β → Prop)
    (hbody : ∀ state, inv state → ∀ flow, body state = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result) :
    ∀ state, inv state → ∀ result, loop body state = ok result → post result := by
  apply loop.fixpoint_induct body
    (fun recur => ∀ state, inv state → ∀ result, recur state = ok result → post result)
  · apply Lean.Order.admissible_pi
    intro state
    apply Lean.Order.admissible_pi
    intro hinv
    apply Lean.Order.admissible_pi
    intro result
    apply Lean.Order.admissible_apply (fun _ value => value = ok result → post result)
    apply Lean.Order.admissible_flatOrder
    simp
  · intro recur ih state hinv result hresult
    cases hstep : body state with
    | fail e => simp [hstep] at hresult
    | div => simp [hstep] at hresult
    | ok flow =>
      have hflow := hbody state hinv flow hstep
      cases flow with
      | cont next => exact ih next hflow result (by simpa [hstep] using hresult)
      | done value =>
        simp only [hstep, ok.injEq] at hresult
        subst result
        exact hflow

end milhouse
