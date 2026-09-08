import Tree.Funs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.utils

/-- The nonempty-map branch performs checked addition before taking the
    maximum with the backing length. Keeping this equation in `Result`
    preserves the overflow behavior instead of assuming it away. -/
theorem updated_length_of_max_index {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (index : Std.Usize) (hmax : mapInst.max_index updates = ok (some index)) :
    updated_length mapInst previous updates = (do
      let next ← index + 1#usize
      ok (core.cmp.impls.OrdUsize.max next previous)) := by
  simp [updated_length, hmax, core.option.Option.map_or,
    updated_length.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeLength.call_once,
    Length.as_usize, liftFun2]

/-- A successful length calculation has exactly the mathematical value
    `max (largest update index + 1) backing_length`. Success supplies the
    overflow check, so no separate arithmetic bounds are assumptions. -/
theorem updated_length_max_spec {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (index length : Std.Usize)
    (hmax : mapInst.max_index updates = ok (some index))
    (hlen : updated_length mapInst previous updates = ok length) :
    length.val = max (index.val + 1) previous.val := by
  rw [updated_length_of_max_index mapInst previous updates index hmax] at hlen
  cases hnext : index + 1#usize with
  | fail e => simp [hnext] at hlen
  | div => simp [hnext] at hlen
  | ok next =>
    simp only [hnext, bind_tc_ok, ok.injEq] at hlen
    have hnext_val : next.val = index.val + 1 := by
      have h := UScalar.add_equiv index 1#usize
      rw [hnext] at h
      simp at h
      omega
    rw [← hlen]
    simp [hnext_val]

/-- Computing the merged length never shortens the backing sequence. -/
theorem updated_length_ge_backing {T U : Type}
    (mapInst : update_map.UpdateMap U T) (previous : Length) (updates : U)
    (length : Std.Usize)
    (hlen : updated_length mapInst previous updates = ok length) :
    previous.val ≤ length.val := by
  cases hmax : mapInst.max_index updates with
  | fail e => simp [updated_length, hmax] at hlen
  | div => simp [updated_length, hmax] at hlen
  | ok largest =>
    cases largest with
    | none =>
      simp [updated_length, hmax, core.option.Option.map_or] at hlen
      subst length
      exact Nat.le_refl _
    | some index =>
      rw [updated_length_max_spec mapInst previous updates index length hmax hlen]
      exact Nat.le_max_right _ _

end milhouse.utils
