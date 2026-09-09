import Tree.ProgressiveTree.Construction.Caches
import Tree.ProgressiveList.Observers

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Every successful public iterator construction initializes all stored
caches to zero. This property requires no hashing, packing, map, cloning,
iterator-output, or finiteness laws. -/
theorem ProgressiveList.try_from_iter_caches_cleared {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self)) :
    self.tree.CachesCleared := by
  unfold ProgressiveList.try_from_iter at hnew
  rw [bind_eq_ok_iff] at hnew
  obtain ⟨status, hbuild, hnew⟩ := hnew
  cases status with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hnew
  | Ok result =>
    obtain ⟨output, length⟩ := result
    simp! only [core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new, bind_tc_ok] at hnew
    rw [bind_eq_ok_iff] at hnew
    obtain ⟨updates, _, hnew⟩ := hnew
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hnew
    subst self
    exact ProgressiveTree.build_from_iter_with_len_caches_cleared ValueInst iterInst input hbuild


theorem ProgressiveList.new_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (values : alloc.vec.Vec T) {self : ProgressiveList T U}
    (hnew : ProgressiveList.new ValueInst mapInst values = ok (.Ok self)) :
    self.tree.CachesCleared :=
  ProgressiveList.try_from_iter_caches_cleared ValueInst mapInst
    (core.iter.traits.collect.IntoIteratorVec T) values hnew

theorem ProgressiveList.try_from_vec_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (values : alloc.vec.Vec T) {self : ProgressiveList T U}
    (hnew : ProgressiveList.Insts.CoreConvertTryFromVecError.try_from
      ValueInst mapInst values = ok (.Ok self)) :
    self.tree.CachesCleared :=
  ProgressiveList.new_caches_cleared ValueInst mapInst values hnew

theorem ProgressiveList.ssz_try_from_iter_caches_cleared {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    {self : ProgressiveList T U}
    (hnew : ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (.Ok self)) :
    self.tree.CachesCleared :=
  ProgressiveList.try_from_iter_caches_cleared ValueInst mapInst iterInst input hnew

theorem ProgressiveList.empty_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {self : ProgressiveList T U}
    (hempty : ProgressiveList.empty ValueInst mapInst = ok self) :
    self.tree.CachesCleared := by
  simp only [ProgressiveList.empty, ProgressiveTree.empty, triomphe.arc.Arc.new,
    bind_tc_ok] at hempty
  rw [bind_eq_ok_iff] at hempty
  obtain ⟨updates, _, hempty⟩ := hempty
  simp only [ok.injEq] at hempty
  subst self
  trivial

theorem ProgressiveList.default_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {self : ProgressiveList T U}
    (hdefault : ProgressiveList.Insts.CoreDefaultDefault.default ValueInst mapInst = ok self) :
    self.tree.CachesCleared :=
  ProgressiveList.empty_caches_cleared ValueInst mapInst hdefault

/-- Newly constructed caches are valid relative to every mathematical
reference hash because they all hold the invalidation sentinel. -/
theorem ProgressiveList.try_from_iter_valid_caches {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I) (input : Input)
    (reference : CacheSubject T → CacheHash) {self : ProgressiveList T U}
    (hnew : ProgressiveList.try_from_iter ValueInst mapInst iterInst input = ok (.Ok self)) :
    self.tree.CachesOn (CacheValidFor reference) 0 :=
  (ProgressiveList.try_from_iter_caches_cleared ValueInst mapInst iterInst input hnew).cachesOn
    (CacheValidFor reference) (CacheValidFor.zero reference) 0

end milhouse.progressive_list
