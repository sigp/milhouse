import Tree.ProgressiveList.Mutable

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Mutable access to a present element succeeds if the one possible fallback
clone succeeds. An existing pending value is returned directly; otherwise the
returned value is the actual clone result, which need not equal the old value. -/
theorem ProgressiveList.get_mut_present_succeeds {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (index : Std.Usize) (old : T)
    (hreads : update_map.GetMutWithReads mapInst self.updates index)
    (hget : ProgressiveList.get ValueInst mapInst self index = ok (some old))
    (hclone : mapInst.get self.updates index = ok none →
      ∃ value, ValueInst.corecloneCloneInst.clone old = ok value) :
    ∃ value back,
      ProgressiveList.get_mut ValueInst mapInst self index = ok (some value, back) ∧
      ((mapInst.get self.updates index = ok (some old) ∧ value = old) ∨
       (mapInst.get self.updates index = ok none ∧
        ValueInst.corecloneCloneInst.clone old = ok value)) := by
  obtain ⟨value, hread, hinitial⟩ : ∃ value,
      (do let (found, _) ← ProgressiveList.get_mut ValueInst mapInst self index
          ok found) = ok (some value) ∧
      ((mapInst.get self.updates index = ok (some old) ∧ value = old) ∨
       (mapInst.get self.updates index = ok none ∧
        ValueInst.corecloneCloneInst.clone old = ok value)) := by
    have hread := ProgressiveList.get_mut_read_eq_pending_or_clone
      ValueInst mapInst self index hreads
    cases hpending : mapInst.get self.updates index with
    | fail e => simp [ProgressiveList.get, hpending] at hget
    | div => simp [ProgressiveList.get, hpending] at hget
    | ok pending =>
      cases pending with
      | none =>
        simp only [ProgressiveList.get, hpending, bind_tc_ok] at hget
        obtain ⟨value, hcloned⟩ := hclone hpending
        refine ⟨value, ?_, Or.inr ⟨rfl, hcloned⟩⟩
        refine hread.trans ?_
        simp only [hpending, bind_tc_ok, hget, core.option.OptionShared0T.cloned,
          hcloned]
      | some pending =>
        have heq : pending = old := by simpa [ProgressiveList.get, hpending] using hget
        subst pending
        refine ⟨old, ?_, Or.inl ⟨rfl, rfl⟩⟩
        refine hread.trans ?_
        simp only [hpending, bind_tc_ok]
  cases hmut : ProgressiveList.get_mut ValueInst mapInst self index with
  | fail e => simp [hmut] at hread
  | div => simp [hmut] at hread
  | ok handle =>
    obtain ⟨found, back⟩ := handle
    simp [hmut] at hread
    subst found
    exact ⟨value, back, rfl, hinitial⟩

end milhouse.progressive_list
