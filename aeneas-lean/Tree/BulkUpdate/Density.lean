import Tree.BulkUpdate.Node
import Tree.BulkUpdate.Window
import Tree.BulkUpdate.RangeExtent
import Tree.UpdateMap.Range

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

private theorem packed_update_dense {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {updates : U} {factor packingDepth prefix1 offset start : Std.Usize}
    {before after : packed_leaf.PackedLeaf T} {newLength : Nat}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    (hlayout : PackingLayout ValueInst (some factor) packingDepth)
    (halign : prefix1.val % factor.val = 0) (hoffset : offset.val % factor.val = 0)
    (hstart : prefix1 + offset = ok start)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) factor.val before.values.val.length newLength)
    (hpos : 0 < newLength) (hcap : newLength ≤ factor.val)
    (hupdate : packed_leaf.PackedLeaf.update ValueInst.tree_hashTreeHashInst
      ValueInst.corecloneCloneInst mapInst before start hash updates =
        ok (core.result.Result.Ok after)) :
    DenseTree (some factor) (.PackedLeaf after) 0 newLength := by
  have hstartVal := usize_add_val hstart
  have hlen := packedLeaf_update_length
    (fun _ _ hget => update_map.get_isSome_iff_hasValueAt hget)
    hlayout.tree_hash_packing_factor_eq
    (by simpa only [leafCapacity] using hlayout.leafCapacity_pos)
    (by simp [hstartVal, Nat.add_mod, halign, hoffset]) hwindow.length_mono
    (by simpa only [hstartVal] using hwindow.extension_complete)
    (by simpa only [hstartVal] using hwindow.updates_bounded) hcap hupdate
  rw [← hlen] at hpos hcap ⊢
  exact .packed factor after hpos hcap

private theorem bulk_capacity_dense_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (oldEnd newEnd : Nat)
    (hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)) :
    ∀ (n : Nat) (depth : Std.Usize) (treeDepth : Nat) (before after : Tree T)
      (prefix1 offset : Std.Usize) (oldLength newLength : Nat),
      2 * depth.val + zeroBit before ≤ n → depth.val = treeDepth →
      UpdateReady factor before treeDepth oldLength →
      prefix1.val % subtreeCapacity factor treeDepth = 0 →
      offset.val % leafCapacity factor = 0 →
      DenseUpdateWindow (update_map.HasValueAt mapInst updates)
        (prefix1.val + offset.val) (subtreeCapacity factor treeDepth) oldLength newLength →
      0 < newLength → newLength ≤ subtreeCapacity factor treeDepth →
      oldLength = min (oldEnd - (prefix1.val + offset.val)) (subtreeCapacity factor treeDepth) →
      newLength = min (newEnd - (prefix1.val + offset.val)) (subtreeCapacity factor treeDepth) →
      BulkRangeOn (update_map.RangePreservesExtentAt mapInst updates oldEnd newEnd)
        mapInst updates factor treeDepth (prefix1.val + offset.val) →
      Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
        ok (core.result.Result.Ok after) →
      subtreeCapacity factor treeDepth < 2 ^ System.Platform.numBits ∧
        DenseTree factor after treeDepth newLength := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro depth treeDepth before after prefix1 offset oldLength newLength
      hmeasure hdepth hready halign hoffset hwindow hpos hcap holdEnd hnewEnd hrange hupdate
    cases hready with
    | leaf value =>
      obtain ⟨result, rfl⟩ := with_updated_leaves_leaf_shape hupdate
      have hlength : newLength = 1 := by
        simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at hcap
        omega
      rw [hlength]
      exact ⟨by simpa [subtreeCapacity, leafCapacity] using (1#usize).hBounds, .leaf result⟩
    | packed factor value hnonempty hfit =>
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
        simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at halign hwindow hcap ⊢
        exact ⟨by simpa using factor.hBounds,
          packed_update_dense ValueInst mapInst hlayout halign hoffset hstart hwindow hpos hcap hresult⟩
    | @node factor oldHash left right child leftLength rightLength hleft hright hshape =>
      obtain ⟨nd, rightPrefix, lo, middle, stop, hash, newLeft, newRight,
        hnd, hrightPrefix, hlo, hmiddle, hstop, rfl, leftStep, rightStep⟩ :=
        Tree.with_updated_leaves_node_step ValueInst mapInst hlayout
          (by simpa only [hdepth] using halign) hupdate
      have hndDepth : nd.val = child := by omega
      have hcapacity : subtreeCapacity factor (child + 1) =
          subtreeCapacity factor child * 2 := by
        simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
      have hrightPrefix' : rightPrefix.val = prefix1.val + subtreeCapacity factor child := by
        simpa only [hndDepth] using hrightPrefix
      have hstop' : stop.val = prefix1.val + offset.val + subtreeCapacity factor (child + 1) := by
        simpa only [hdepth] using hstop
      have hfull : 0 < rightLength → leftLength = subtreeCapacity factor child := by
        rcases hshape with ⟨_, hz⟩ | ⟨_, hfull⟩
        · omega
        · exact hfull
      have hwindow' := hwindow
      rw [hcapacity] at hwindow'
      obtain ⟨leftWindow, rightWindow⟩ := hwindow'.split hleft.length_le_capacity hfull
      have rightWindow' : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
          (rightPrefix.val + offset.val) (subtreeCapacity factor child) rightLength
            (newLength - subtreeCapacity factor child) := by
        have heq : rightPrefix.val + offset.val =
            (prefix1.val + offset.val) + subtreeCapacity factor child := by omega
        simpa only [heq] using rightWindow
      have halignLeft : prefix1.val % subtreeCapacity factor child = 0 := by
        apply mod_half_eq_zero
        rwa [← hcapacity]
      have halignRight : rightPrefix.val % subtreeCapacity factor child = 0 := by
        rw [hrightPrefix', Nat.add_mod_right]
        exact halignLeft
      have childCorrect : ∀ (old new : Tree T) (start lo hi : Std.Usize) (oldLen newLen : Nat),
          DenseTree factor old child oldLen → start.val % subtreeCapacity factor child = 0 →
          lo.val = start.val + offset.val →
          hi.val = start.val + offset.val + subtreeCapacity factor child →
          DenseUpdateWindow (update_map.HasValueAt mapInst updates)
            (start.val + offset.val) (subtreeCapacity factor child) oldLen newLen →
          newLen ≤ subtreeCapacity factor child →
          oldLen = min (oldEnd - (start.val + offset.val)) (subtreeCapacity factor child) →
          newLen = min (newEnd - (start.val + offset.val)) (subtreeCapacity factor child) →
          update_map.RangePreservesExtentAt mapInst updates oldEnd newEnd lo hi →
          (mapInst.has_any_in_range updates lo hi = ok true →
            BulkRangeOn (update_map.RangePreservesExtentAt mapInst updates oldEnd newEnd)
              mapInst updates factor child (start.val + offset.val)) →
          Tree.BulkChildStep ValueInst mapInst updates old new start offset nd lo hi hashes →
          DenseTree factor new child newLen := by
        intro old new start lo hi oldLen newLen hdense halign hlo hhi hwindow hcap
          holdEnd hnewEnd hlocal hdescend hstep
        rcases hstep with ⟨hempty, rfl⟩ | ⟨hhas, hupdate⟩
        · have heq := hlocal.empty_length hempty
          have hlength : newLen = oldLen := by omega
          rwa [hlength]
        · have hinside := hlocal.selected_inside hhas
          have hchildPos := hlayout.subtreeCapacity_pos child
          have hpositive : 0 < newLen := by omega
          have hsmall : 2 * nd.val + zeroBit old < n := by
            have := zeroBit_le_one old
            simp only [zeroBit] at hmeasure
            omega
          exact (ih _ hsmall nd child old new start offset oldLen newLen
            (Nat.le_refl _) hndDepth (.ofDense hdense) halign hoffset hwindow hpositive hcap holdEnd hnewEnd (hdescend hhas) hupdate).2
      have hleftCap := hleft.length_le_capacity
      have hrightCap := hright.length_le_capacity
      have holdEnd' := holdEnd
      have hnewEnd' := hnewEnd
      rw [hcapacity] at holdEnd' hnewEnd'
      have hnewLeft := childCorrect left newLeft prefix1 lo middle leftLength
        (min newLength (subtreeCapacity factor child)) hleft halignLeft hlo (by omega)
        leftWindow (Nat.min_le_right _ _) (by omega) (by omega)
        (hrange.left_query (hi := middle) hlo (by omega))
        (fun hselected => hrange.left (hi := middle) hlo (by omega) hselected) leftStep
      have hnewRight := childCorrect right newRight rightPrefix middle stop rightLength
        (newLength - subtreeCapacity factor child) hright halignRight hmiddle (by omega)
        rightWindow' (by omega) (by omega) (by omega)
        (hrange.right_query (lo := middle) (hi := stop) (by omega) (by omega))
        (fun hselected => by
          have h := hrange.right (lo := middle) (hi := stop) (by omega) (by omega) hselected
          simpa only [hrightPrefix', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h) rightStep
      have hcapBound : subtreeCapacity factor (child + 1) < 2 ^ System.Platform.numBits := by
        have hstopBound : stop.val < 2 ^ System.Platform.numBits := by simpa using stop.hBounds
        omega
      refine ⟨hcapBound, ?_⟩
      have hsum : newLength = min newLength (subtreeCapacity factor child) +
          (newLength - subtreeCapacity factor child) := by omega
      rw [hsum]
      exact .node factor hash newLeft newRight child _ _ hnewLeft hnewRight (by omega) (by omega)
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
          rw [bind_eq_ok_iff] at hupdate
          obtain ⟨cloned, hcloned, hupdate⟩ := hupdate
          cases cloned with
          | none =>
            simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hupdate
          | some value =>
            simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
              Tree.leaf_with_hash, leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new,
              triomphe.arc.Arc.new] at hupdate
            subst after
            have hlength : newLength = 1 := by
              simp [subtreeCapacity, leafCapacity] at hcap
              omega
            rw [hlength]
            exact ⟨by simpa [subtreeCapacity, leafCapacity] using (1#usize).hBounds, .leaf _⟩
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
            simp [subtreeCapacity, leafCapacity] at halign hwindow hcap ⊢
            refine ⟨by simpa using factor.hBounds,
              packed_update_dense ValueInst mapInst hlayout halign hoffset hstart ?_ hpos hcap hresult⟩
            simpa [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using hwindow
      · rw [if_neg hz, bind_eq_ok_iff] at hupdate
        obtain ⟨nd, hnd, hupdate⟩ := hupdate
        have hndVal := usize_sub_one_val hnd
        simp only [Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          bind_tc_ok] at hupdate
        have hsmall : 2 * depth.val + zeroBit (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T) < n := by
          simp only [zeroBit] at hmeasure ⊢
          omega
        have hexpanded : UpdateReady factor (Tree.Node hash (.Zero nd) (.Zero nd) : Tree T) depth.val 0 := by
          rw [hndVal]
          exact .node factor hash (.Zero nd) (.Zero nd) nd.val 0 0
            (.zero factor nd) (.zero factor nd) (Or.inl ⟨rfl, rfl⟩)
        exact ih _ hsmall depth depth.val (Tree.Node hash (.Zero nd) (.Zero nd)) after
          prefix1 offset 0 newLength (Nat.le_refl _) rfl hexpanded halign hoffset
          hwindow hpos hcap holdEnd hnewEnd hrange hupdate

/-- Density preservation needs only the numeric effects of reached range
answers: skipped windows retain their occupied extent and selected windows
start inside the final prefix. No range-value reflection or clone identity is
needed. Global prefix endpoints are clipped to the actual binary window. -/
theorem Tree.with_updated_leaves_capacity_dense_of_range_extents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {prefix1 offset depth : Std.Usize} {oldEnd newEnd : Nat}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hrange : BulkRangeOn (update_map.RangePreservesExtentAt mapInst updates oldEnd newEnd)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val
      (min (oldEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val)))
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val)
      (min (oldEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val))
      (min (newEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val)))
    (hpos : prefix1.val + offset.val < newEnd)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after)) :
    subtreeCapacity factor depth.val < 2 ^ System.Platform.numBits ∧
      DenseTree factor after depth.val
        (min (newEnd - (prefix1.val + offset.val)) (subtreeCapacity factor depth.val)) := by
  have hcapacity := hlayout.subtreeCapacity_pos depth.val
  exact bulk_capacity_dense_aux ValueInst mapInst updates hlayout oldEnd newEnd hashes
    (2 * depth.val + zeroBit before) depth depth.val before after prefix1 offset _ _
    (Nat.le_refl _) rfl (.ofDense hdense) halign hoffset hwindow (by omega)
    (Nat.min_le_right _ _) rfl rfl hrange hupdate

/-- A successful update of a dense binary subtree preserves density at the
    new window length, including nonzero global offsets used by progressive
    layers. Successful arithmetic also certifies representable capacity.
    Cloning may change values; no clone-identity law is needed for density. -/
theorem Tree.with_updated_leaves_capacity_dense {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {before after : Tree T} {prefix1 offset depth : Std.Usize} {oldLength newLength : Nat}
    {hashes : Option (alloc.collections.btree.map.BTreeMap (Std.Usize × Std.Usize)
      (alloy_primitives.bits.fixed.FixedBytes 32#usize) Global)}
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hpos : 0 < newLength) (hcap : newLength ≤ subtreeCapacity factor depth.val)
    (hupdate : Tree.with_updated_leaves ValueInst mapInst before updates prefix1 offset depth hashes =
      ok (core.result.Result.Ok after)) :
    subtreeCapacity factor depth.val < 2 ^ System.Platform.numBits ∧
      DenseTree factor after depth.val newLength := by
  have hold : min ((prefix1.val + offset.val + oldLength) - (prefix1.val + offset.val))
      (subtreeCapacity factor depth.val) = oldLength := by
    have := hdense.length_le_capacity
    omega
  have hnew : min ((prefix1.val + offset.val + newLength) - (prefix1.val + offset.val))
      (subtreeCapacity factor depth.val) = newLength := by omega
  have hresult := Tree.with_updated_leaves_capacity_dense_of_range_extents
    ValueInst mapInst updates hlayout (hrange.preservesExtents_of_window hwindow)
    (by simpa only [hold] using hdense) halign hoffset
    (by simpa only [hold, hnew] using hwindow) (by omega) hupdate
  simpa only [hnew] using hresult


end milhouse.tree
