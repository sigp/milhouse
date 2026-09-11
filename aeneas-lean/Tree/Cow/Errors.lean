import Tree.Cow.Consuming

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.cow

/-- Every Rust-level consuming error is a missing entry and restores the
original handle through every continuation input. This needs no clone,
entry, or metadata law. Panic/divergence in Aeneas Result is a separate outcome. -/
theorem Cow.into_mut_error_restores {T : Type} (cloneInst : core.clone.Clone T)
    (self : Cow T) {error : error.Error}
    {back : core.result.Result T milhouse.error.Error → Cow T}
    (hmut : Cow.into_mut cloneInst self = ok (.Err error, back)) :
    error = milhouse.error.Error.CowMissingEntry ∧ ∀ returned, back returned = self := by
  cases self with
  | BTree inner action =>
    cases inner with
    | Mutable original =>
      simp [Cow.into_mut, BTreeCow.into_mut_inner, CowOnMut.run_eq] at hmut
    | Immutable original entry =>
      cases entry with
      | none =>
        rw [(Cow.into_mut_missing_entry cloneInst original action).1] at hmut
        have heq := Result.ok.inj hmut
        have herr := (core.result.Result.Err.inj (congrArg Prod.fst heq)).symm
        have hback := (congrArg Prod.snd heq).symm
        exact ⟨herr, fun returned => congrFun hback returned⟩
      | some entry =>
        cases hclone : cloneInst.clone original <;>
          simp [Cow.into_mut, BTreeCow.into_mut_inner, hclone,
            alloc.collections.btree.map.entry.VacantEntry.insert, CowOnMut.run_eq] at hmut
  | Vec inner action =>
    cases inner with
    | Mutable original =>
      simp [Cow.into_mut, VecCow.into_mut_inner, CowOnMut.run_eq] at hmut
    | Immutable original entry =>
      cases entry with
      | none =>
        rw [(Cow.into_mut_missing_entry cloneInst original action).2] at hmut
        have heq := Result.ok.inj hmut
        have herr := (core.result.Result.Err.inj (congrArg Prod.fst heq)).symm
        have hback := (congrArg Prod.snd heq).symm
        exact ⟨herr, fun returned => congrFun hback returned⟩
      | some entry =>
        cases hclone : cloneInst.clone original with
        | fail e => simp [Cow.into_mut, VecCow.into_mut_inner, hclone] at hmut
        | div => simp [Cow.into_mut, VecCow.into_mut_inner, hclone] at hmut
        | ok value =>
          cases hinsert : vec_map.VacantEntry.insert entry value with
          | fail e => simp [Cow.into_mut, VecCow.into_mut_inner, hclone, hinsert] at hmut
          | div => simp [Cow.into_mut, VecCow.into_mut_inner, hclone, hinsert] at hmut
          | ok result =>
            obtain ⟨found, entryBack⟩ := result
            simp [Cow.into_mut, VecCow.into_mut_inner, hclone, hinsert, CowOnMut.run_eq] at hmut

end milhouse.cow
