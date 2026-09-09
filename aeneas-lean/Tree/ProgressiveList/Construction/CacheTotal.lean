import Tree.ProgressiveList.Construction.Total
import Tree.ProgressiveList.Construction.Caches

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Total public construction establishes indexed contents, valid backing,
no pending updates, and valid caches relative to any mathematical reference
hash. Cache initialization adds no premise to the existing total specification. -/
theorem ProgressiveList.try_from_iter_total_cache_spec {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (reference : CacheSubject T → CacheHash)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.try_from_iter ValueInst mapInst iterInst input =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false ∧
      self.tree.CachesOn (CacheValidFor reference) 0 := by
  obtain ⟨self, hnew, hrep, hbacking, hspine, hpending⟩ :=
    ProgressiveList.try_from_iter_total_spec ValueInst mapInst iterInst input values hyields
      hlayout hfits updates hdefault hget hmax hempty
  exact ⟨self, hnew, hrep, hbacking, hspine, hpending,
    ProgressiveList.try_from_iter_valid_caches ValueInst mapInst iterInst input reference hnew⟩

/-- Total vector construction also establishes valid caches, without an
iterator or element-hashing premise. -/
theorem ProgressiveList.new_total_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (reference : CacheSubject T → CacheHash) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.new ValueInst mapInst values = ok (core.result.Result.Ok self) ∧
      self.Represents ValueInst mapInst values.val ∧ self.BackingValid factor ∧
      self.SpineValid factor ∧ ProgressiveList.has_pending_updates ValueInst mapInst self = ok false ∧
      self.tree.CachesOn (CacheValidFor reference) 0 :=
  ProgressiveList.try_from_iter_total_cache_spec ValueInst mapInst reference
    (core.iter.traits.collect.IntoIteratorVec T) values values.val (vec_into_iterator_yields values)
    hlayout hfits updates hdefault hget hmax hempty

/-- The actual vector conversion has the complete total cache specification. -/
theorem ProgressiveList.try_from_vec_total_cache_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (reference : CacheSubject T → CacheHash) (values : alloc.vec.Vec T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.val.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.CoreConvertTryFromVecError.try_from ValueInst mapInst values =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst values.val ∧
      self.BackingValid factor ∧ self.SpineValid factor ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false ∧
      self.tree.CachesOn (CacheValidFor reference) 0 :=
  ProgressiveList.new_total_cache_spec ValueInst mapInst reference values hlayout hfits updates hdefault hget hmax hempty

/-- The actual SSZ iterator-construction trait has the complete total cache
specification. All builder cache obligations are proved internally. -/
theorem ProgressiveList.ssz_try_from_iter_total_cache_spec {T U Input I : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (reference : CacheSubject T → CacheHash)
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T)
    (hyields : IntoIteratorYields iterInst input values)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none) (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeTry_from_iterTryFromIterTError.try_from_iter
      ValueInst mapInst iterInst input = ok (core.result.Result.Ok self) ∧
      self.Represents ValueInst mapInst values ∧ self.BackingValid factor ∧
      self.SpineValid factor ∧ ProgressiveList.has_pending_updates ValueInst mapInst self = ok false ∧
      self.tree.CachesOn (CacheValidFor reference) 0 :=
  ProgressiveList.try_from_iter_total_cache_spec ValueInst mapInst reference iterInst input values hyields hlayout hfits
    updates hdefault hget hmax hempty

end milhouse.progressive_list
