import Tree.PackedLeaf.BulkUpdate
import Tree.BulkUpdate.CloneScope

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.packed_leaf

/-- Correct contents throughout the packed window are equivalent to identity
on retained stored slots and pending values. Overwritten stored copies need no
identity law. No input density or external termination law is assumed. -/
theorem PackedLeaf.update_contents_iff_retained_clones {T U : Type}
    {thi : tree_hash.TreeHash T} {cloneInst : core.clone.Clone T}
    {mapInst : update_map.UpdateMap U T} {updates : U}
    {self result : PackedLeaf T} {prefix1 factor : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    (hfactor : thi.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0)
    (hupdate : PackedLeaf.update thi cloneInst mapInst self prefix1 hash updates = ok (.Ok result)) :
    (∀ (query : Std.Usize) (pending : Option T), prefix1.val ≤ query.val →
      query.val < prefix1.val + factor.val → mapInst.get updates query = ok pending →
      result.values.val[query.val - prefix1.val]? = pending.or self.values.val[query.val - prefix1.val]?) ↔
      tree.PackedRetainedCloneOn (fun value => cloneInst.clone value = ok value)
        mapInst updates factor.val self prefix1.val ∧
      (∀ (query : Std.Usize) value, prefix1.val ≤ query.val → query.val < prefix1.val + factor.val →
        mapInst.get updates query = ok (some value) → cloneInst.clone value = ok value) := by
  constructor
  · intro hcontents
    constructor
    · intro query value hlo hhi hget hvalue
      have hidentity := (PackedLeaf.get_after_update_iff_clone_visible
        hfactor halign hlo hhi hget hupdate).mp (hcontents query none hlo hhi hget)
      exact hidentity value (by simpa only [Option.none_or] using hvalue)
    · intro query value hlo hhi hget
      have hidentity := (PackedLeaf.get_after_update_iff_clone_visible
        hfactor halign hlo hhi hget hupdate).mp (hcontents query (some value) hlo hhi hget)
      exact hidentity value (by simp)
  · rintro ⟨hstored, hpending⟩ query pending hlo hhi hget
    exact PackedLeaf.get_after_update_of_clone_on_window hstored hpending hfactor halign hlo hhi hget hupdate

end milhouse.packed_leaf
