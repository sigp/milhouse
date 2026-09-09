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
  induction orig generalizing base after depth with
  | ProgressiveZero =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same _ _ hstop =>
      exact ⟨ProgressiveTree.rebaseOrigCachesOn_of_caches ValueInst.corecmpPartialEqInst P _ _ _ hcache,
        ProgressiveTree.rebaseBaseCachesOn_of_stop ValueInst.corecmpPartialEqInst P _ _ _ hstop⟩
  | ProgressiveNode origHash origLeft origRight ih =>
    cases ProgressiveTree.rebase_on_recursive_step ValueInst hlayout hrebase with
    | same _ _ hstop =>
      exact ⟨ProgressiveTree.rebaseOrigCachesOn_of_caches ValueInst.corecmpPartialEqInst P _ _ _ hcache,
        ProgressiveTree.rebaseBaseCachesOn_of_stop ValueInst.corecmpPartialEqInst P _ _ _ hstop⟩
    | @node _ baseHash _ baseLeft _ baseRight newRight start capacity binary fullDepth origLeftLength baseLeftLength next
        action hstart hnext hcapacity hbinary horigLength hbaseLength hfullDepth hleft hright hpointer =>
      obtain ⟨hleftFit, hrightFit⟩ := hfit
      have horigLengthVal := ProgressiveTree.rebase_layer_length ValueInst hlayout hleftFit
        hstart hnext hcapacity hbinary horigLength
      have hbaseLengthVal := ProgressiveTree.rebase_layer_length ValueInst hlayout hleftFit
        hstart hnext hcapacity hbinary hbaseLength
      have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
      have hfullDepthVal := usize_add_val hfullDepth
      have horigLeft : DenseTree factor origLeft (2 * depth.val) origLeftLength.val := by
        simpa only [horigLengthVal] using horig.split_layer.1
      have hbaseLeft : DenseTree factor baseLeft (2 * depth.val) baseLeftLength.val := by
        simpa only [hbaseLengthVal] using hbase.split_layer.1
      have hleftInputs := Tree.rebase_on_cache_inputs ValueInst hlayout P
        (by omega) horigLeft hbaseLeft (hequality hpointer).1 (hhashes hpointer).1 hleft hcache.2.1
      have hleftContents := Tree.rebase_on_contents_correct ValueInst hlayout
        (by omega) horigLeft hbaseLeft (hequality hpointer).1 (hhashes hpointer).1 hleft
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hnext] at hadd
      simp at hadd
      have hnextVal : next.val = depth.val + 1 := by omega
      have horigRight : origRight.Dense factor next.val (origLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using horig.right_remainder
      have hbaseRight : baseRight.Dense factor next.val (baseLength.val - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using hbase.right_remainder
      have hnewFit : origRight.Fits factor next.val := by simpa only [hnextVal] using hrightFit
      have hrightInputs := ih horigRight hbaseRight hnewFit (hequality hpointer).2 (hhashes hpointer).2
        hright (by simpa only [hnextVal] using hcache.2.2)
      have hrightContents := ProgressiveTree.rebase_on_recursive_preserves_contents ValueInst hlayout
        horigRight hbaseRight hnewFit (hequality hpointer).2 (hhashes hpointer).2 hright
      refine ⟨⟨fun _ => ⟨?_, hleftInputs.1, ?_⟩, fun hnot => (hnot hpointer).elim⟩,
        fun _ => ⟨hleftInputs.2, ?_⟩⟩
      · simpa only [hleftContents.1, hrightContents] using hcache.1
      · simpa only [hnextVal] using hrightInputs.1
      · simpa only [hnextVal] using hrightInputs.2

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
