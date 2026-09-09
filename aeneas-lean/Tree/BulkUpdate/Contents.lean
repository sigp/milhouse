import Tree.BulkUpdate.Node
import Tree.UpdateMap.Range

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Contents of a bulk-update result within its assigned window. Pending
    values override existing slots; missing map entries preserve them. The
    offset maps binary-tree indices to container-wide update-map keys. -/
def Tree.BulkContents {T U : Type} (mapInst : update_map.UpdateMap U T) (updates : U)
    (factor : Option Std.Usize) (before after : Tree T) (depth start offset : Nat) : Prop :=
  ∀ (query : Std.Usize) (pending : Option T), mapInst.get updates query = ok pending →
    start + offset ≤ query.val → query.val < start + offset + subtreeCapacity factor depth →
    after.slot factor depth (query.val - offset) =
      pending.or (before.slot factor depth (query.val - offset))

private theorem bind_eq_ok_iff {A B : Type} {x : Result A}
    {f : A → Result B} {y : B} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp [Bind.bind, Std.bind]

private def zeroBit {T : Type} : Tree T → Nat
  | .Zero _ => 1
  | _ => 0

private theorem zeroBit_le_one {T : Type} (self : Tree T) : zeroBit self ≤ 1 := by
  cases self <;> simp [zeroBit]

/-- At an unpacked leaf, the window contains exactly the consumed update key. -/
theorem Tree.bulkContents_of_leaf_value {T U : Type}
    {mapInst : update_map.UpdateMap U T} {updates : U} {before : Tree T}
    {after : leaf.Leaf T} {index prefix1 offset : Std.Usize}
    (hindex : prefix1 + offset = ok index)
    (hget : mapInst.get updates index = ok (some after.value)) :
    Tree.BulkContents mapInst updates none before (.Leaf after) 0 prefix1.val offset.val := by
  intro query pending hquery hlo hhi
  have hindexVal := usize_add_val hindex
  simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at hhi
  have heq : query = index := by scalar_tac
  subst query
  rw [hget] at hquery
  cases hquery
  rfl

/-- Lift packed-leaf bulk-update contents through the global offset used by
    binary-tree updates. Both starts are aligned to the packing factor. Clone
    identity is scoped to this leaf's stored values and pending window. -/
theorem Tree.bulkContents_of_packed_update {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {updates : U} {before after : packed_leaf.PackedLeaf T}
    {factor prefix1 offset start : Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    (hcloneStored : ∀ value ∈ before.values.val, ValueInst.corecloneCloneInst.clone value = ok value)
    (hclonePending : ∀ (query : Std.Usize) value, start.val ≤ query.val →
      query.val < start.val + factor.val → mapInst.get updates query = ok (some value) →
      ValueInst.corecloneCloneInst.clone value = ok value)
    (hfactor : ValueInst.tree_hashTreeHashInst.tree_hash_packing_factor = ok factor)
    (halign : prefix1.val % factor.val = 0) (hoffset : offset.val % factor.val = 0)
    (hstart : prefix1 + offset = ok start)
    (hupdate : packed_leaf.PackedLeaf.update ValueInst.tree_hashTreeHashInst
      ValueInst.corecloneCloneInst mapInst before start hash updates = ok (core.result.Result.Ok after)) :
    Tree.BulkContents mapInst updates (some factor) (.PackedLeaf before) (.PackedLeaf after)
      0 prefix1.val offset.val := by
  intro query pending hquery hlo hhi
  have hstartVal := usize_add_val hstart
  simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at hhi
  have hstartAlign : start.val % factor.val = 0 := by simp [hstartVal, Nat.add_mod, halign, hoffset]
  have hmod : (query.val - offset.val) % factor.val = query.val - start.val := by
    rw [mod_eq_sub_of_aligned halign (by omega) (by omega)]
    omega
  have hread := packed_leaf.PackedLeaf.get_after_update_of_clone_on_window
    hcloneStored hclonePending hfactor hstartAlign
    (by omega) (by omega) hquery hupdate
  simpa only [Tree.slot, leafCapacity, hmod] using hread

private theorem bulk_shape_contents_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    (hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)) :
    ∀ (n : Nat) (depth : Std.Usize) (treeDepth : Nat) (before after : Tree T)
      (prefix1 offset : Std.Usize),
      2 * depth.val + zeroBit before ≤ n → depth.val = treeDepth →
      before.Shape factor treeDepth →
      prefix1.val % subtreeCapacity factor treeDepth = 0 →
      offset.val % leafCapacity factor = 0 →
      Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
        ok (core.result.Result.Ok after) →
      subtreeCapacity factor treeDepth < 2 ^ System.Platform.numBits ∧ after.Shape factor treeDepth ∧
        Tree.BulkContents mapInst updates factor before after treeDepth prefix1.val offset.val := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro depth treeDepth before after prefix1 offset hmeasure hdepth hshape halign hoffset hupdate
    cases hshape with
    | leaf value =>
      obtain ⟨_, index, result, hindex, hget, rfl⟩ :=
        Tree.with_updated_leaves_leaf_value ValueInst mapInst (fun _ value _ _ => hclone value) hupdate
      exact ⟨by simpa [subtreeCapacity, leafCapacity] using (1#usize).hBounds,
        .leaf result, Tree.bulkContents_of_leaf_value hindex hget⟩
    | packed factor value =>
      have hz : depth = 0#usize := by scalar_tac
      subst depth
      unfold Tree.with_updated_leaves at hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨opt, hopt, hupdate⟩ := hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨hash, hhash, hupdate⟩ := hupdate
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
        exact ⟨by simpa [subtreeCapacity, leafCapacity] using factor.hBounds, .packed factor result,
          Tree.bulkContents_of_packed_update ValueInst mapInst
            (fun value _ => hclone value) (fun _ value _ _ _ => hclone value)
            hlayout.tree_hash_packing_factor_eq
            (by simpa [subtreeCapacity, leafCapacity] using halign) hoffset hstart hresult⟩
    | @node factor left right child oldHash hleft hright =>
      obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
        hnd, hrightPrefix, hlo, hmiddle, hstop, rfl, leftStep, rightStep⟩ :=
        Tree.with_updated_leaves_node_step ValueInst mapInst hlayout
          (by simpa [hdepth] using halign) hupdate
      have hndDepth : nd.val = child := by omega
      have hcapacity : subtreeCapacity factor (child + 1) =
          subtreeCapacity factor child * 2 := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
      have hrightPrefix' : rightPrefix.val = prefix1.val + subtreeCapacity factor child := by
        simpa [hndDepth] using hrightPrefix
      have hstop' : stop.val = prefix1.val + offset.val + subtreeCapacity factor (child + 1) := by
        simpa [hdepth] using hstop
      have halignLeft : prefix1.val % subtreeCapacity factor child = 0 := by
        apply mod_half_eq_zero
        rwa [← hcapacity]
      have halignRight : rightPrefix.val % subtreeCapacity factor child = 0 := by
        rw [hrightPrefix', Nat.add_mod_right]
        exact halignLeft
      have childCorrect : ∀ (old new : Tree T) (start lo hi : Std.Usize),
          old.Shape factor child → start.val % subtreeCapacity factor child = 0 →
          lo.val = start.val + offset.val →
          hi.val = start.val + offset.val + subtreeCapacity factor child →
          Tree.BulkChildStep ValueInst mapInst updates old new start offset nd lo hi hashes →
          new.Shape factor child ∧
            Tree.BulkContents mapInst updates factor old new child start.val offset.val := by
        intro old new start lo hi hshape halign hlo hhi hstep
        rcases hstep with ⟨hempty, rfl⟩ | ⟨_, hupdate⟩
        · refine ⟨hshape, ?_⟩
          intro query pending hget hqueryLo hqueryHi
          have hnone := hrange lo hi query pending hempty hget (by omega) (by omega)
          subst pending
          rfl
        · have hsmall : 2 * nd.val + zeroBit old < n := by
            have := zeroBit_le_one old
            simp only [zeroBit] at hmeasure
            omega
          exact (ih (2 * nd.val + zeroBit old) hsmall nd child old new start offset
            (Nat.le_refl _) hndDepth hshape halign hoffset hupdate).2
      obtain ⟨hnewLeft, hleftContents⟩ := childCorrect left newLeft prefix1 lo middle
        hleft halignLeft hlo (by omega) leftStep
      obtain ⟨hnewRight, hrightContents⟩ := childCorrect right newRight rightPrefix middle stop
        hright halignRight hmiddle (by omega) rightStep
      have hcapBound : subtreeCapacity factor (child + 1) < 2 ^ System.Platform.numBits := by
        have hstopBound : stop.val < 2 ^ System.Platform.numBits := by simpa using stop.hBounds
        omega
      refine ⟨hcapBound, .node hash hnewLeft hnewRight, ?_⟩
      intro query pending hquery hqueryLo hqueryHi
      have hmod := mod_eq_sub_of_aligned halign
        (show prefix1.val ≤ query.val - offset.val by omega)
        (show query.val - offset.val < prefix1.val + subtreeCapacity factor (child + 1) by omega)
      change (if (query.val - offset.val) % subtreeCapacity factor (child + 1) < subtreeCapacity factor child
          then newLeft.slot factor child (query.val - offset.val)
          else newRight.slot factor child (query.val - offset.val)) =
        pending.or (if (query.val - offset.val) % subtreeCapacity factor (child + 1) < subtreeCapacity factor child
          then left.slot factor child (query.val - offset.val)
          else right.slot factor child (query.val - offset.val))
      rw [hmod]
      by_cases hroute : query.val - offset.val - prefix1.val < subtreeCapacity factor child
      · simp only [if_pos hroute]
        exact hleftContents query pending hquery hqueryLo (by omega)
      · simp only [if_neg hroute]
        exact hrightContents query pending hquery (by omega) (by omega)
    | zero factor zeroDepth =>
      have heq : zeroDepth = depth := by scalar_tac
      subst zeroDepth
      unfold Tree.with_updated_leaves at hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨opt, hopt, hupdate⟩ := hupdate
      rw [bind_eq_ok_iff] at hupdate
      obtain ⟨hash, hhash, hupdate⟩ := hupdate
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
            simp [core.option.OptionShared0T.cloned, hclone, core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch, Tree.leaf_with_hash,
              leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new] at hupdate
            subst after
            exact ⟨by simpa [subtreeCapacity, leafCapacity] using (1#usize).hBounds,
              .leaf { hash, value }, Tree.bulkContents_of_leaf_value hindex hfound⟩
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
            refine ⟨by simpa [subtreeCapacity, leafCapacity] using factor.hBounds,
              .packed factor result, ?_⟩
            have hcontents := Tree.bulkContents_of_packed_update ValueInst mapInst
              (fun value _ => hclone value) (fun _ value _ _ _ => hclone value) hfactor
              (by simpa [subtreeCapacity, leafCapacity] using halign) hoffset hstart hresult
            simpa [Tree.BulkContents, Tree.slot, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using hcontents
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
        obtain ⟨hcapBound, hshape, hcontents⟩ := ih _ hsmall depth depth.val
          (Tree.Node hash (.Zero nd) (.Zero nd)) after prefix1 offset (Nat.le_refl _) rfl
          hexpanded halign hoffset hupdate
        refine ⟨hcapBound, hshape, ?_⟩
        intro query pending hquery hlo hhi
        have hzslot : (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T).slot factor depth.val
            (query.val - offset.val) = none := by
          rw [hndVal]
          simp [Tree.slot]
        have h := hcontents query pending hquery hlo hhi
        change after.slot factor depth.val (query.val - offset.val) = pending.or none
        simpa only [hzslot] using h

/-- Successful bulk updates also certify that the whole binary capacity fits
    in a machine word. This result packages that bound with shape and contents
    so callers can derive surrounding window geometry from the update itself. -/
theorem Tree.with_updated_leaves_capacity_shape_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {before after : Tree T} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hshape : before.Shape factor depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after)) :
    subtreeCapacity factor depth.val < 2 ^ System.Platform.numBits ∧
      after.Shape factor depth.val ∧
      Tree.BulkContents mapInst updates factor before after depth.val prefix1.val offset.val := by
  exact bulk_shape_contents_aux ValueInst mapInst updates hlayout hclone hrange hashes
    (2 * depth.val + zeroBit before) depth depth.val before after prefix1 offset
    (Nat.le_refl _) rfl hshape halign hoffset hupdate

/-- Successful binary-tree bulk updates preserve geometric shape and apply
    pending values exactly throughout their assigned window. This includes
    node recursion and zero expansion. Density is not needed for content
    correctness; range queries only need to exclude values when reporting an
    empty range. -/
theorem Tree.with_updated_leaves_shape_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {before after : Tree T} {prefix1 offset depth : Std.Usize}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hshape : before.Shape factor depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after)) :
    after.Shape factor depth.val ∧
      Tree.BulkContents mapInst updates factor before after depth.val prefix1.val offset.val := by
  exact (Tree.with_updated_leaves_capacity_shape_contents ValueInst mapInst updates
    hlayout hclone hrange hshape halign hoffset hupdate).2

/-- Bulk-update correctness through extracted lookup, at every index in the
    assigned binary window. The shift bound follows from successful updates;
    callers supply no extra machine-arithmetic precondition. -/
theorem Tree.get_after_with_updated_leaves {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hclone : ∀ value, ValueInst.corecloneCloneInst.clone value = ok value)
    (hrange : update_map.RangeExcludesValues mapInst updates)
    {before after : Tree T} {prefix1 offset depth index query : Std.Usize} {pending : Option T}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hshape : before.Shape factor depth.val)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hquery : query.val = index.val + offset.val)
    (hindexLo : prefix1.val ≤ index.val)
    (hindexHi : index.val < prefix1.val + subtreeCapacity factor depth.val)
    (hget : mapInst.get updates query = ok pending)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after)) :
    Tree.get_recursive ValueInst after index depth packingDepth = (do
      let previous ← Tree.get_recursive ValueInst before index depth packingDepth
      ok (pending.or previous)) := by
  obtain ⟨hcapacity, hafter, hcontents⟩ :=
    bulk_shape_contents_aux ValueInst mapInst updates hlayout hclone hrange hashes
      (2 * depth.val + zeroBit before) depth depth.val before after prefix1 offset
      (Nat.le_refl _) rfl hshape halign hoffset hupdate
  have hbits : depth.val + packingDepth.val ≤ System.Platform.numBits := by
    rw [hlayout.subtreeCapacity_eq_two_pow] at hcapacity
    by_contra hnot
    have hle : System.Platform.numBits ≤ packingDepth.val + depth.val := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    omega
  rw [hafter.get_recursive_eq_slot hlayout depth rfl hbits,
    hshape.get_recursive_eq_slot hlayout depth rfl hbits]
  simp only [bind_tc_ok]
  apply congrArg ok
  have hread := hcontents query pending hget (by omega) (by omega)
  have hlocal : query.val - offset.val = index.val := by omega
  simpa only [hlocal] using hread

end milhouse.tree
