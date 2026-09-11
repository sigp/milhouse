import Tree.BulkUpdate.CloneIdentity

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private def zeroBit {T : Type} : Tree T → Nat
  | .Zero _ => 1
  | _ => 0

private theorem zeroBit_le_one {T : Type} (self : Tree T) : zeroBit self ≤ 1 := by
  cases self <;> simp [zeroBit]

private theorem retained_clones_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)) :
    ∀ (n : Nat) (depth : Std.Usize) (treeDepth : Nat) (before after : Tree T)
      (prefix1 offset : Std.Usize),
      2 * depth.val + zeroBit before ≤ n → depth.val = treeDepth →
      before.Shape factor treeDepth →
      prefix1.val % subtreeCapacity factor treeDepth = 0 →
      offset.val % leafCapacity factor = 0 →
      Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes = ok (.Ok after) →
      Tree.BulkContents mapInst updates factor before after treeDepth prefix1.val offset.val →
      before.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        mapInst updates factor treeDepth (prefix1.val + offset.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro depth treeDepth before after prefix1 offset hmeasure hdepth hshape halign hoffset hupdate hcontents
    cases hshape with
    | leaf value =>
      obtain ⟨_, index, pending, result, hindex, hget, hclone, rfl⟩ :=
        Tree.with_updated_leaves_leaf_cloned ValueInst mapInst hupdate
      exact ⟨True.intro, hcontents.leaf_clone_identity hindex hget hclone⟩
    | packed factor value =>
      have hz : depth = 0#usize := by scalar_tac
      subst depth
      unfold Tree.with_updated_leaves at hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨opt, _, hupdate⟩ := hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨hash, _, hupdate⟩ := hupdate
      change (prefix1 + offset >>= _) = _ at hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨start, hstart, hupdate⟩ := hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨result, hresult, hupdate⟩ := hupdate
      cases result with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hupdate
      | Ok result =>
        simp [core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new] at hupdate
        subst after
        exact (Tree.bulkContents_packed_iff_retained_clones ValueInst mapInst
          hlayout.tree_hash_packing_factor_eq
          (by simpa [subtreeCapacity, leafCapacity] using halign) hoffset hstart hresult).mp hcontents
    | @node factor left right child oldHash hleft hright =>
      obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
        hnd, hrightPrefix, hlo, hmiddle, hstop, rfl, leftStep, rightStep⟩ :=
        Tree.with_updated_leaves_node_step ValueInst mapInst hlayout
          (by simpa only [hdepth] using halign) hupdate
      have hndDepth : nd.val = child := by omega
      have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
      have hrightPrefix' : rightPrefix.val = prefix1.val + subtreeCapacity factor child := by
        simpa only [hndDepth] using hrightPrefix
      have hstop' : stop.val = prefix1.val + offset.val + subtreeCapacity factor (child + 1) := by
        simpa only [hdepth] using hstop
      have halignLeft : prefix1.val % subtreeCapacity factor child = 0 := by
        apply mod_half_eq_zero
        rwa [← hcapacity]
      have halignRight : rightPrefix.val % subtreeCapacity factor child = 0 := by
        rw [hrightPrefix', Nat.add_mod_right]
        exact halignLeft
      have hsmall (old : Tree T) : 2 * nd.val + zeroBit old < n := by
        have := zeroBit_le_one old
        simp only [zeroBit] at hmeasure
        omega
      constructor
      · intro queryLo queryHi hqueryLo hqueryHi hselected
        have heqLo : queryLo = lo := by scalar_tac
        have heqHi : queryHi = middle := by scalar_tac
        subst queryLo
        subst queryHi
        rcases leftStep with ⟨hempty, _⟩ | ⟨_, hleftUpdate⟩
        · rw [hselected] at hempty
          cases hempty
        · exact ih _ (hsmall left) nd child left newLeft prefix1 offset (Nat.le_refl _)
            hndDepth hleft halignLeft hoffset hleftUpdate (hcontents.node_left halign)
      · intro queryLo queryHi hqueryLo hqueryHi hselected
        have heqLo : queryLo = middle := by scalar_tac
        have heqHi : queryHi = stop := by scalar_tac
        subst queryLo
        subst queryHi
        rcases rightStep with ⟨hempty, _⟩ | ⟨_, hrightUpdate⟩
        · rw [hselected] at hempty
          cases hempty
        · have hrightContents : Tree.BulkContents mapInst updates factor right newRight child
              rightPrefix.val offset.val := by
            simpa only [hrightPrefix'] using hcontents.node_right halign
          simpa only [hrightPrefix', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih _ (hsmall right) nd child right newRight rightPrefix offset (Nat.le_refl _)
              hndDepth hright halignRight hoffset hrightUpdate hrightContents
    | zero factor zeroDepth =>
      have heq : zeroDepth = depth := by scalar_tac
      subst zeroDepth
      unfold Tree.with_updated_leaves at hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨opt, _, hupdate⟩ := hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨hash, _, hupdate⟩ := hupdate
      change (if depth = depth then _ else _) = _ at hupdate
      rw [if_pos rfl] at hupdate
      by_cases hz : depth = 0#usize
      · subst depth
        simp only [hlayout.opt_packing_factor_eq, bind_tc_ok] at hupdate
        cases factor with
        | none =>
          simp only [core.option.Option.is_some, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨index, hindex, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨found, hfound, hupdate⟩ := hupdate
          cases found with
          | none =>
            simp [core.option.OptionShared0T.cloned, core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | some value =>
            cases hclone : ValueInst.corecloneCloneInst.clone value with
            | fail error => simp [core.option.OptionShared0T.cloned, hclone] at hupdate
            | div => simp [core.option.OptionShared0T.cloned, hclone] at hupdate
            | ok copied =>
              simp [core.option.OptionShared0T.cloned, hclone, core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch, Tree.leaf_with_hash,
                leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
              subst after
              exact ⟨True.intro, hcontents.leaf_clone_identity hindex hfound hclone⟩
        | some factor =>
          have hfactor := hlayout.tree_hash_packing_factor_eq
          simp only [core.option.Option.is_some, Option.isSome, ↓reduceIte, packed_leaf.PackedLeaf.empty,
            alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new,
            hfactor, bind_tc_ok] at hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨start, hstart, hupdate⟩ := hupdate
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨result, hresult, hupdate⟩ := hupdate
          cases result with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | Ok result =>
            simp [core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new] at hupdate
            subst after
            have hpacked := (Tree.bulkContents_packed_iff_retained_clones ValueInst mapInst hfactor
              (by simpa [subtreeCapacity, leafCapacity] using halign) hoffset hstart hresult).mp (by
                simpa [Tree.BulkContents, Tree.slot, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using hcontents)
            exact ⟨True.intro, hpacked.2⟩
      · rw [if_neg hz, bind_eq_ok_iff] at hupdate
        obtain ⟨nd, hnd, hupdate⟩ := hupdate
        have hndVal := usize_sub_one_val hnd
        simp only [Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          bind_tc_ok] at hupdate
        have hsmall : 2 * depth.val + zeroBit (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T) < n := by
          simp only [zeroBit] at hmeasure ⊢
          omega
        have hexpanded : Tree.Shape factor (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T) depth.val := by
          rw [hndVal]
          exact .node hash (.zero factor nd) (.zero factor nd)
        have hcontentsExpanded : Tree.BulkContents mapInst updates factor
            (.Node hash (.Zero nd) (.Zero nd)) after depth.val prefix1.val offset.val := by
          intro query pending hquery hlo hhi
          have h := hcontents query pending hquery hlo hhi
          have hzslot : (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T).slot factor depth.val
              (query.val - offset.val) = none := by
            rw [hndVal]
            simp [Tree.slot]
          change after.slot factor depth.val (query.val - offset.val) =
            pending.or ((Tree.Node hash (.Zero nd) (.Zero nd) : Tree T).slot factor depth.val
              (query.val - offset.val))
          rw [hzslot]
          exact h
        have hclone := ih _ hsmall depth depth.val
          (Tree.Node hash (.Zero nd) (.Zero nd)) after prefix1 offset (Nat.le_refl _) rfl
          hexpanded halign hoffset hupdate hcontentsExpanded
        rw [hndVal] at hclone ⊢
        exact (Tree.BulkCloneScope.zero_expand _ _ mapInst updates factor depth nd nd.val _ hash).mpr hclone

/-- Correct contents after successful binary rebuilding force identity of
every selected pending clone and retained stored clone. Layout, input shape,
and alignment identify the actual slots. No range-correctness, clone,
termination, density, or capacity law is assumed. -/
theorem Tree.with_updated_leaves_retained_clone_identity {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hshape : before.Shape factor depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after))
    (hcontents : Tree.BulkContents mapInst updates factor before after depth.val prefix1.val offset.val) :
    before.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
      mapInst updates factor depth.val (prefix1.val + offset.val) :=
  retained_clones_aux ValueInst mapInst updates hlayout hashes
    (2 * depth.val + zeroBit before) depth depth.val before after prefix1 offset
    (Nat.le_refl _) rfl hshape halign hoffset hupdate hcontents

/-- Under exclusion of pending values in skipped binary windows, correct
contents are equivalent to retained and pending clone identity. The necessity
direction above does not require that range law. -/
theorem Tree.with_updated_leaves_contents_iff_retained_clones {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {updates : U} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hrange : BulkRangeOn (update_map.RangeExcludesValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hshape : before.Shape factor depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth hashes = ok (.Ok after)) :
    Tree.BulkContents mapInst updates factor before after depth.val prefix1.val offset.val ↔
      before.BulkRetainedCloneOn (fun value => ValueInst.corecloneCloneInst.clone value = ok value)
        mapInst updates factor depth.val (prefix1.val + offset.val) := by
  constructor
  · exact Tree.with_updated_leaves_retained_clone_identity ValueInst mapInst hlayout
      hshape halign hoffset hupdate
  · intro hclone
    exact (Tree.with_updated_leaves_shape_contents ValueInst mapInst updates hlayout
      hclone hrange hshape halign hoffset hupdate).2

end milhouse.tree
