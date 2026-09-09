import Tree.ProgressiveTree.Rebase.Caches
import Tree.Rebase.CacheReflection

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- A cache-valid successful progressive result supplies both selected input
laws. Reused nodes retain the actual child-call evidence, so this also covers
the final pointer checks. No input-cache validity is assumed. -/
theorem ProgressiveTree.rebase_on_recursive_cache_inputs {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize} {depth : Std.U32}
    (horig : orig.Dense factor depth.val (origLength.val - progressiveCapacity factor depth.val))
    (hbase : base.Dense factor depth.val (baseLength.val - progressiveCapacity factor depth.val))
    (hfit : orig.Fits factor depth.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth = ok (.Ok after))
    (hcache : after.CachesOn P depth.val) :
    orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth.val ∧
      orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth.val := by
  have hcontent := ProgressiveTree.rebaseContentInputs_of_dense ValueInst hlayout
    (origLength := origLength.val) (baseLength := baseLength.val) horig hbase hfit hequality hhashes
  apply (ProgressiveTree.rebaseCacheInputs_iff_of_dense ValueInst hlayout P
    (origLength := origLength.val) (baseLength := baseLength.val) horig hbase hfit).mp
  exact (ProgressiveTree.rebase_on_recursive_cache_iff_of_inputs ValueInst P hcontent hrebase).mp hcache

/-- Cache validity of a successful public progressive rebase entails the
retained-original and imported-base laws at the starting layer. -/
theorem ProgressiveTree.rebase_on_cache_inputs {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (horig : orig.Dense factor 0 origLength.val) (hbase : base.Dense factor 0 baseLength.val)
    (hfit : orig.Fits factor 0)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after))
    (hcache : after.CachesOn P 0) :
    orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base 0 ∧
      orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base 0 := by
  have horig' : orig.Dense factor (0#u32).val (origLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using horig
  have hbase' : base.Dense factor (0#u32).val (baseLength.val - progressiveCapacity factor (0#u32).val) := by
    simpa [progressiveCapacity] using hbase
  exact ProgressiveTree.rebase_on_recursive_cache_inputs ValueInst hlayout P
    horig' hbase' hfit hequality hhashes hrebase hcache

/-- Under the semantic content laws and input geometry, the selected cache
laws are jointly necessary and sufficient for the successful result's cache
validity. No cache-validity premise is assumed by the equivalence. -/
theorem ProgressiveTree.rebase_on_cache_iff {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base after : ProgressiveTree T} {origLength baseLength : Std.Usize}
    (horig : orig.Dense factor 0 origLength.val) (hbase : base.Dense factor 0 baseLength.val)
    (hfit : orig.Fits factor 0)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok after)) :
    after.CachesOn P 0 ↔
      orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base 0 ∧
        orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base 0 := by
  constructor
  · exact ProgressiveTree.rebase_on_cache_inputs ValueInst hlayout P horig hbase hfit hequality hhashes hrebase
  · rintro ⟨horigCache, hbaseCache⟩
    exact (ProgressiveTree.rebase_on_cache_spec ValueInst hlayout P
      horig hbase hfit hequality hhashes horigCache hbaseCache hrebase).2

end milhouse.progressive_tree
