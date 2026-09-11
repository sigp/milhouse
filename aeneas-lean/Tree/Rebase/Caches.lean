import Tree.Rebase.SelectedCaches
import Tree.Rebase.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Successful binary rebasing preserves contents and every cache predicate
indexed by logical input and depth. The semantic comparison laws establish unchanged
child contents before an original parent cache is reused. Original validity
is required only for retained caches; base validity is required only for
imported caches. Both scopes follow the input-based action categories.
No hash computation, cache write, or assumed child execution is needed. -/
theorem Tree.rebase_on_cache_spec {T : Type} (ValueInst : Value T)
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
    (horigCache : orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth)
    (hbaseCache : orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth)
    (hrebase : Tree.rebase_on ValueInst orig base (some (origLength, baseLength)) fullDepth =
      ok (core.result.Result.Ok action)) :
    action.ContentsCorrect orig base ∧ (applyRebaseAction orig action).CachesOn P depth := by
  have hcontent := Tree.rebaseContentInputs_of_dense ValueInst hlayout hdepth horig hbase hequality hhashes
  refine ⟨Tree.rebase_on_contents_correct ValueInst hlayout
    hdepth horig hbase hequality hhashes hrebase, ?_⟩
  apply (Tree.rebase_on_cache_iff_of_inputs ValueInst P
    (lengths := some (origLength, baseLength)) (fullDepth := fullDepth) hcontent hrebase).mpr
  exact (Tree.rebaseCacheInputs_iff_of_dense ValueInst hlayout P hdepth horig hbase).mpr
    ⟨horigCache, hbaseCache⟩

end milhouse.tree
