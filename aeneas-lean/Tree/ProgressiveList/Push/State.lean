import Tree.ProgressiveList.Push

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- The only returned Rust error from `push` is `ListFull` at the maximum
logical length, and it restores the entire input state. This equivalence
requires no representation, map, cloning, or backing invariant. Failures or
divergence in length evaluation or insertion are not returned Rust errors. -/
theorem ProgressiveList.push_error_iff_full {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (value : T)
    {error : error.Error} {result : ProgressiveList T U} :
    ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Err error, result) ↔
      ProgressiveList.len ValueInst mapInst self = ok core.num.Usize.MAX ∧
        error = .ListFull core.num.Usize.MAX ∧ result = self := by
  constructor
  · intro hpush
    cases hlen : ProgressiveList.len ValueInst mapInst self with
    | fail e => simp [ProgressiveList.push, hlen] at hpush
    | div => simp [ProgressiveList.push, hlen] at hpush
    | ok index =>
      by_cases hfull : index = core.num.Usize.MAX
      · subst index
        rw [ProgressiveList.push_full ValueInst mapInst self value hlen] at hpush
        have hstate : error = .ListFull core.num.Usize.MAX ∧ result = self := by
          simpa only [ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] using hpush.symm
        exact ⟨rfl, hstate⟩
      · cases hins : mapInst.insert self.updates index value with
        | fail e => simp [ProgressiveList.push, hlen, hfull, hins] at hpush
        | div => simp [ProgressiveList.push, hlen, hfull, hins] at hpush
        | ok inserted =>
          obtain ⟨previous, updates⟩ := inserted
          simp [ProgressiveList.push, hlen, hfull, hins] at hpush
  · rintro ⟨hlen, herror, hresult⟩
    rw [herror, hresult]
    exact ProgressiveList.push_full ValueInst mapInst self value hlen

end milhouse.progressive_list
