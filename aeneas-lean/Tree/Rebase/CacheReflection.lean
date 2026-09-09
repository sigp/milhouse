import Tree.Rebase.Caches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Every valid successful result supplies both selected input-cache laws.
The semantic comparison laws identify retained caches' logical subjects;
no original/base cache validity or assumed child result is a premise. -/
theorem Tree.rebase_on_cache_inputs {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base : Tree T} {depth : Nat} {origLength baseLength fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hdepth : fullDepth.val = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength.val)
    (hbase : DenseTree factor base depth baseLength.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth = ok (.Ok action))
    (hcache : (applyRebaseAction orig action).CachesOn P depth) :
    orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth ∧
      orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth := by
  have hcontent := Tree.rebaseContentInputs_of_dense ValueInst hlayout hdepth horig hbase hequality hhashes
  apply (Tree.rebaseCacheInputs_iff_of_dense ValueInst hlayout P hdepth horig hbase).mp
  exact (Tree.rebase_on_cache_iff_of_inputs ValueInst P
    (lengths := some (origLength, baseLength)) (fullDepth := fullDepth) hcontent hrebase).mp hcache

/-- Under the semantic content laws and accurate dense metadata, the two
selected input-cache laws are jointly necessary and sufficient for cache
validity after successful rebasing. No cache premise is assumed by this iff. -/
theorem Tree.rebase_on_cache_iff {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base : Tree T} {depth : Nat} {origLength baseLength fullDepth : Std.Usize}
    {action : RebaseAction (Tree T)}
    (hdepth : fullDepth.val = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength.val)
    (hbase : DenseTree factor base depth baseLength.val)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth = ok (.Ok action)) :
    (applyRebaseAction orig action).CachesOn P depth ↔
      orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth ∧
        orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth := by
  constructor
  · exact Tree.rebase_on_cache_inputs ValueInst hlayout P hdepth horig hbase hequality hhashes hrebase
  · rintro ⟨horigCache, hbaseCache⟩
    exact (Tree.rebase_on_cache_spec ValueInst hlayout P hdepth horig hbase
      hequality hhashes horigCache hbaseCache hrebase).2

end milhouse.tree
