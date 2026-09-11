import Tree.ProgressiveList.Clone
import Tree.ProgressiveList.CopyOnWrite
import Tree.ProgressiveList.IterCow.State
import Tree.HashCache.Validity
import Tree.ProgressiveTree.HashCache

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Every returned push state preserves backing caches. Push changes only
the pending map, and full-list rejection preserves the complete state. -/
theorem ProgressiveList.push_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self : ProgressiveList T U) (value : T) (hcache : self.tree.CachesOn P 0)
    {status : core.result.Result Unit error.Error} {result : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value = ok (status, result)) :
    result.tree.CachesOn P 0 := by
  unfold ProgressiveList.push at hpush
  rw [builder.bind_eq_ok_iff] at hpush
  obtain ⟨index, _, hpush⟩ := hpush
  split at hpush
  · simp only [ok.injEq, Prod.mk.injEq] at hpush
    obtain ⟨rfl, rfl⟩ := hpush
    exact hcache
  · rw [builder.bind_eq_ok_iff] at hpush
    obtain ⟨⟨previous, updates⟩, _, hpush⟩ := hpush
    simp! only [ok.injEq, Prod.mk.injEq] at hpush
    obtain ⟨rfl, rfl⟩ := hpush
    exact hcache

/-- Every mutable continuation preserves the backing caches, independently
of its returned value or the pending map's write-back behavior. -/
theorem ProgressiveList.get_mut_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self : ProgressiveList T U) (index : Std.Usize) (hcache : self.tree.CachesOn P 0)
    {value : Option T} {back : Option T → ProgressiveList T U}
    (hmut : ProgressiveList.get_mut ValueInst mapInst self index = ok (value, back)) :
    ∀ replacement, (back replacement).tree.CachesOn P 0 := by
  obtain ⟨mapBack, _, rfl⟩ := ProgressiveList.get_mut_success ValueInst mapInst self index hmut
  exact fun _ => hcache

/-- Returning any CoW handle changes only pending updates, including handles
changed through the extracted consuming mutation operation. -/
theorem ProgressiveList.get_cow_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self : ProgressiveList T U) (index : Std.Usize) (hcache : self.tree.CachesOn P 0)
    {handle : Option (cow.Cow T)} {back : Option (cow.Cow T) → ProgressiveList T U}
    (hcow : ProgressiveList.get_cow ValueInst mapInst self index = ok (handle, back)) :
    ∀ replacement, (back replacement).tree.CachesOn P 0 := by
  obtain ⟨fallback, mapBack, _, rfl⟩ := ProgressiveList.get_cow_success ValueInst mapInst self index hcow
  exact fun _ => hcache

/-- Cloning shares the backing tree, so every cache predicate survives
without element-clone or pending-map clone laws. -/
theorem ProgressiveList.clone_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self : ProgressiveList T U) (hcache : self.tree.CachesOn P 0)
    {result : ProgressiveList T U}
    (hclone : ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst self = ok result) :
    result.tree.CachesOn P 0 := by
  obtain ⟨updates, _, rfl⟩ := ProgressiveList.clone_success_state ValueInst mapInst self hclone
  exact hcache

theorem ProgressiveList.iter_cow_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self : ProgressiveList T U) (hcache : self.tree.CachesOn P 0)
    {cursor : ProgressiveListIterCow T U} {back : ProgressiveListIterCow T U → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow ValueInst mapInst self = ok (cursor, back)) :
    ∀ replacement, (back replacement).tree.CachesOn P 0 := by
  obtain ⟨_, _, rfl⟩ := ProgressiveList.iter_cow_success_state ValueInst mapInst self hiter
  exact fun _ => hcache

/-- Every bounded CoW iterator constructor continuation preserves caches,
including errors and arbitrary changed-cursor inputs. No iterator-stepping
or borrowing behavior is assumed. -/
theorem ProgressiveList.iter_cow_from_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (self : ProgressiveList T U) (index : Std.Usize) (hcache : self.tree.CachesOn P 0)
    {result : core.result.Result (ProgressiveListIterCow T U) error.Error}
    {back : core.result.Result (ProgressiveListIterCow T U) error.Error → ProgressiveList T U}
    (hiter : ProgressiveList.iter_cow_from ValueInst mapInst self index = ok (result, back)) :
    ∀ replacement, (back replacement).tree.CachesOn P 0 := by
  cases result with
  | Err err =>
    intro replacement
    rw [ProgressiveList.iter_cow_from_error_preserves_self ValueInst mapInst self index hiter replacement]
    exact hcache
  | Ok cursor =>
    obtain ⟨_, _, hok, herr⟩ := ProgressiveList.iter_cow_from_success_state ValueInst mapInst self index hiter
    intro replacement
    cases replacement with
    | Ok changed => rw [hok]; exact hcache
    | Err err => rw [herr]; exact hcache

end milhouse.progressive_list
