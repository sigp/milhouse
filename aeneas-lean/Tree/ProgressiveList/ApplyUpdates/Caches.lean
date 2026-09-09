import Tree.ProgressiveTree.BulkUpdate.Caches
import Tree.ProgressiveList.ApplyUpdates
import Tree.HashCache.Validity

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Every returned application state preserves cache invariants accepting
zero. Success clears rebuilt caches and preserves untouched subtrees; Rust
errors restore the whole list. No representation, backing, clone, map, default,
packing, or termination law is needed for this preservation result. -/
theorem ProgressiveList.apply_updates_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (hzero : ∀ subject, P subject (Array.repeat 32#usize 0#u8))
    (self : ProgressiveList T U) (hcache : self.tree.CachesOn P 0)
    {result : ProgressiveList T U} {outcome : core.result.Result Unit error.Error}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (outcome, result)) :
    result.tree.CachesOn P 0 := by
  cases outcome with
  | Err e =>
    rw [ProgressiveList.apply_updates_error_preserves_self ValueInst mapInst self happly]
    exact hcache
  | Ok u =>
    cases u
    rcases ProgressiveList.apply_updates_success_state ValueInst mapInst self happly with
      ⟨_, rfl⟩ | ⟨defaults, length, newTree, _, _, _, htree, rfl⟩
    · exact hcache
    · exact progressive_tree.ProgressiveTree.with_updated_leaves_preserves_caches
        ValueInst mapInst self.updates P hzero hcache htree

/-- Applying updates preserves validity relative to a mathematical reference
hash, including on returned errors. The only input invariant concerns the
existing caches; zero-cache validity is supplied by the specification itself. -/
theorem ProgressiveList.apply_updates_preserves_valid_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (reference : CacheSubject T → CacheHash)
    (self : ProgressiveList T U) (hcache : self.tree.CachesOn (CacheValidFor reference) 0)
    {result : ProgressiveList T U} {outcome : core.result.Result Unit error.Error}
    (happly : ProgressiveList.apply_updates ValueInst mapInst self = ok (outcome, result)) :
    result.tree.CachesOn (CacheValidFor reference) 0 :=
  ProgressiveList.apply_updates_preserves_caches ValueInst mapInst (CacheValidFor reference)
    (CacheValidFor.zero reference) self hcache happly

end milhouse.progressive_list
