import Tree.ProgressiveList.Clone.Total
import Tree.ProgressiveList.Caches

open Aeneas Aeneas.Std Result
open milhouse milhouse.progressive_tree

namespace milhouse.progressive_list

/-- The actual inherited `clone_from` replaces the destination by a clone of
the source, including the source clone's failure or divergence. It calls the
source pending map's `clone`, with no destination-map clone law required. -/
theorem ProgressiveList.clone_from_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (destination source : ProgressiveList T U) :
    (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source =
    ProgressiveList.Insts.CoreCloneClone.clone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst source := rfl

/-- The extraction-only Rust caller selects exactly the public trait method
proved here; it does not substitute a separate clone implementation. -/
theorem ProgressiveList.clone_from_caller_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (destination source : ProgressiveList T U) :
    proof_roots.progressive_list_clone_from ValueInst mapInst destination source =
    (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source := rfl

/-- Success depends only on the actual source pending-map clone. -/
theorem ProgressiveList.clone_from_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (destination source : ProgressiveList T U) :
    (∃ result, (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source = ok result) ↔
    ∃ updates, mapInst.corecloneCloneInst.clone source.updates = ok updates := by
  simpa only [ProgressiveList.clone_from_eq] using
    ProgressiveList.clone_success_iff ValueInst mapInst source

/-- A successful `clone_from` represents the source contents under only the
source map clone's read/extent laws. The old destination may be arbitrary,
and the copied map's maximum need not equal the source map's maximum. -/
theorem ProgressiveList.clone_from_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (destination source : ProgressiveList T U) (contents : _root_.List T)
    (hrep : source.Represents ValueInst mapInst contents)
    (hmapGet : ∀ updates, mapInst.corecloneCloneInst.clone source.updates = ok updates →
      ∀ query, mapInst.get updates query = mapInst.get source.updates query)
    (hmapMax : ∀ updates, mapInst.corecloneCloneInst.clone source.updates = ok updates →
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim source.length.val
          (fun index => max (index.val + 1) source.length.val) = contents.length)
    {result : ProgressiveList T U}
    (hclone : (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source = ok result) :
    result.Represents ValueInst mapInst contents := by
  rw [ProgressiveList.clone_from_eq] at hclone
  exact ProgressiveList.clone_represents ValueInst mapInst source contents hrep hmapGet hmapMax hclone

/-- Source backing validity survives successful replacement without element
or pending-map semantics, and without a destination invariant. -/
theorem ProgressiveList.clone_from_preserves_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} (destination source : ProgressiveList T U)
    (hbacking : source.BackingValid factor) {result : ProgressiveList T U}
    (hclone : (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source = ok result) :
    result.BackingValid factor := by
  rw [ProgressiveList.clone_from_eq] at hclone
  exact ProgressiveList.clone_preserves_backing ValueInst mapInst source hbacking hclone

/-- All source backing-cache predicates survive the replacement. No property
of the old destination caches or of element/pending-map cloning is required. -/
theorem ProgressiveList.clone_from_preserves_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (P : CacheSubject T → CacheHash → Prop)
    (destination source : ProgressiveList T U) (hcache : source.tree.CachesOn P 0)
    {result : ProgressiveList T U}
    (hclone : (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source = ok result) :
    result.tree.CachesOn P 0 := by
  rw [ProgressiveList.clone_from_eq] at hclone
  exact ProgressiveList.clone_preserves_caches ValueInst mapInst P source hcache hclone

/-- The source pending-update observer transfers under just its corresponding
map clone law, independently of representation and other map observers. -/
theorem ProgressiveList.has_pending_updates_after_clone_from {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (destination source : ProgressiveList T U)
    (hmapEmpty : ∀ updates, mapInst.corecloneCloneInst.clone source.updates = ok updates →
      mapInst.is_empty updates = mapInst.is_empty source.updates)
    {result : ProgressiveList T U}
    (hclone : (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source = ok result) :
    ProgressiveList.has_pending_updates ValueInst mapInst result =
      ProgressiveList.has_pending_updates ValueInst mapInst source := by
  rw [ProgressiveList.clone_from_eq] at hclone
  exact ProgressiveList.has_pending_updates_after_clone ValueInst mapInst source hmapEmpty hclone

/-- Total source-sequence replacement, preserving source backing validity and
exact backing fields and returning the actual source pending-map clone. Only
that clone's termination, read agreement, and logical extent are assumed;
maximum identity is unnecessary. There are no laws on the destination,
element cloning, packing, or map `clone_from`. -/
theorem ProgressiveList.clone_from_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} (destination source : ProgressiveList T U) (contents : _root_.List T)
    (hrep : source.Represents ValueInst mapInst contents) (hbacking : source.BackingValid factor)
    (hmap : ∃ updates, mapInst.corecloneCloneInst.clone source.updates = ok updates ∧
      (∀ query, mapInst.get updates query = mapInst.get source.updates query) ∧
      ∃ largest, mapInst.max_index updates = ok largest ∧
        largest.elim source.length.val
          (fun index => max (index.val + 1) source.length.val) = contents.length) :
    ∃ result, (ProgressiveList.Insts.CoreCloneClone ValueInst.corecloneCloneInst ValueInst
      mapInst.corecloneCloneInst mapInst).clone_from destination source = ok result ∧
      result.Represents ValueInst mapInst contents ∧ result.BackingValid factor ∧
      result.tree = source.tree ∧ result.length = source.length ∧
      mapInst.corecloneCloneInst.clone source.updates = ok result.updates := by
  simpa only [ProgressiveList.clone_from_eq] using
    ProgressiveList.clone_total_spec ValueInst mapInst source contents hrep hbacking hmap

end milhouse.progressive_list
