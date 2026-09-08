import Tree.Lemmas
import Tree.PackedLeaf.BulkUpdate

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

/-- A successful bulk update of an unpacked leaf consumes the map value at
    `prefix + offset` and stores that value. Success supplies both depth zero
    and successful checked index arithmetic; no map metadata laws are needed. -/
theorem Tree.with_updated_leaves_leaf_value {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    {self : leaf.Leaf T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    {updated : Tree T}
    (hupdate : Tree.with_updated_leaves ValueInst mapInst (.Leaf self) updates
      prefix1 offset depth hashes = ok (core.result.Result.Ok updated)) :
    depth = 0#usize ∧ ∃ index result,
      prefix1 + offset = ok index ∧ mapInst.get updates index = ok (some result.value) ∧
      updated = Tree.Leaf result := by
  unfold Tree.with_updated_leaves at hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨opt, hopt, hupdate⟩ := hupdate
  rw [bind_eq_ok_iff] at hupdate
  obtain ⟨hash, hhash, hupdate⟩ := hupdate
  by_cases hdepth : depth = 0#usize
  · rw [if_pos hdepth, bind_eq_ok_iff] at hupdate
    obtain ⟨index, hindex, hupdate⟩ := hupdate
    rw [bind_eq_ok_iff] at hupdate
    obtain ⟨found, hfound, hupdate⟩ := hupdate
    cases found with
    | none =>
      simp [core.option.OptionShared0T.cloned, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at hupdate
    | some value =>
      simp [core.option.OptionShared0T.cloned, hclone, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch, Tree.leaf_with_hash,
        leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
      exact ⟨hdepth, index, { hash, value }, hindex, hfound, hupdate.symm⟩
  · simp [hdepth] at hupdate

/-- Reading a bulk-updated unpacked leaf returns the exact pending map value
    used for the update. This connects the content result to extracted lookup. -/
theorem Tree.get_after_with_updated_leaves_leaf {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    {self : leaf.Leaf T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    {updated : Tree T}
    (hupdate : Tree.with_updated_leaves ValueInst mapInst (.Leaf self) updates
      prefix1 offset depth hashes = ok (core.result.Result.Ok updated))
    (query packingDepth : Std.Usize) :
    ∃ index, prefix1 + offset = ok index ∧
      Tree.get_recursive ValueInst updated query depth packingDepth = mapInst.get updates index := by
  obtain ⟨rfl, index, result, hindex, hget, rfl⟩ :=
    Tree.with_updated_leaves_leaf_value ValueInst mapInst hclone hupdate
  exact ⟨index, hindex, (get_recursive_leaf ValueInst result query packingDepth).trans hget.symm⟩

end milhouse.tree
