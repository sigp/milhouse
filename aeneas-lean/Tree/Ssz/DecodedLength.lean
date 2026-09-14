import Tree.Ssz.VariableStep

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.ssz_items

private theorem bind_eq_ok_iff {A B : Type} {x : Result A} {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ value, x = ok value ∧ f value = ok y := by
  cases x <;> simp

private theorem next_variable_value_index (bytes part : Slice Std.U8)
    (first count index offset : Std.Usize) (rest : SszItems)
    (hnext : SszItems.next (.Variable bytes first count index offset) =
      ok (some (core.result.Result.Ok part), rest)) :
    ∃ successor nextOffset, rest = .Variable bytes first count successor nextOffset ∧
      successor.val = index.val + 1 ∧ index.val ≤ count.val := by
  simp only [SszItems.next] at hnext
  split at hnext
  · simp only [ok.injEq, Prod.mk.injEq] at hnext
    cases hnext.1
  · rename_i hlive
    simp only [bind_eq_ok_iff] at hnext
    obtain ⟨successor, hadd, ⟨item, nextOffset⟩, hitem, hresult⟩ := hnext
    simp! only [ok.injEq, Prod.mk.injEq] at hresult
    refine ⟨successor, nextOffset, hresult.2.symm, ?_, not_lt.mp hlive⟩
    have hsum := UScalar.add_equiv index 1#usize
    rw [hadd] at hsum
    exact hsum.2.1

/-- A variable cursor can decode no more values than the number of remaining
table entries. This holds for arbitrary element behavior and either exhaustion
or an error, without canonical-byte, offset-order, or builder assumptions. -/
theorem SszItems.decodes_variable_length_le {T : Type}
    (decode : Slice Std.U8 → Result (core.result.Result T ssz.decode.DecodeError))
    (bytes : Slice Std.U8) (first count index offset : Std.Usize)
    (values : _root_.List T) (error : Option ssz.decode.DecodeError)
    (hdecode : (.Variable bytes first count index offset : SszItems).Decodes decode values error) :
    values.length ≤ count.val + 1 - index.val := by
  generalize heq : (SszItems.Variable bytes first count index offset) = items at hdecode
  induction hdecode generalizing index offset with
  | exhausted => simp
  | boundary_error => simp
  | element_error => simp
  | @cons items rest part value values error hnext hvalue htail ih =>
    subst items
    obtain ⟨successor, nextOffset, hrest, hsuccessor, hlive⟩ :=
      next_variable_value_index bytes part first count index offset rest hnext
    have hlength := ih successor nextOffset hrest.symm
    simp only [_root_.List.length_cons]
    omega

end milhouse.ssz_items
