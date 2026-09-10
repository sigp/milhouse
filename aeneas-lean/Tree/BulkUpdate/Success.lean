import Tree.BulkUpdate.RangeScope
import Tree.BulkUpdate.Activation
import Tree.BulkUpdate.ActivationNecessary
import Tree.BulkUpdate.GuardsNecessary
import Tree.BulkUpdate.Arithmetic
import Tree.BulkUpdate.Density
import Tree.BulkUpdate.Contents
import Tree.PackedLeaf.BulkUpdateSuccess

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

private def zeroBit {T : Type} : Tree T → Nat
  | .Zero _ => 1
  | _ => 0

private theorem zeroBit_le_one {T : Type} (self : Tree T) : zeroBit self ≤ 1 := by
  cases self <;> simp [zeroBit]

private theorem opt_hash_none (depth prefix1 : Std.Usize) :
    utils.opt_hash none depth prefix1 = ok none := by rfl

private theorem default_hash :
    core.option.Option.unwrap_or_default
      (alloy_primitives.bits.fixed.FixedBytes.Insts.CoreDefaultDefault 32#usize) none =
        ok (Array.repeat 32#usize 0#u8) := by rfl

private theorem bulk_update_success_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found) :
    ∀ (n : Nat) (depth : Std.Usize) (treeDepth : Nat) (before : Tree T)
      (prefix1 offset : Std.Usize) (oldLength newLength : Nat),
      2 * depth.val + zeroBit before ≤ n → depth.val = treeDepth →
      UpdateReady factor before treeDepth oldLength →
      prefix1.val % subtreeCapacity factor treeDepth = 0 →
      offset.val % leafCapacity factor = 0 →
      prefix1.val + offset.val + subtreeCapacity factor treeDepth ≤ Std.Usize.max →
      DenseUpdateWindow (update_map.HasValueAt mapInst updates)
        (prefix1.val + offset.val) (subtreeCapacity factor treeDepth) oldLength newLength →
      newLength ≤ subtreeCapacity factor treeDepth →
      BulkGuardsPass mapInst updates factor treeDepth (prefix1.val + offset.val) →
      before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
        mapInst updates factor treeDepth (prefix1.val + offset.val) →
      BulkRangeOn (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
        mapInst updates factor treeDepth (prefix1.val + offset.val) →
      ∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
        prefix1 offset depth none = ok (core.result.Result.Ok after) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro depth treeDepth before prefix1 offset oldLength newLength hmeasure hdepth
      hready halign hoffset hend hwindow hcapacity hguards hclone hqueries
    obtain ⟨start, hstart, hstartVal⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := prefix1) (y := offset)
        (by rw [UScalar.max_USize_eq]; omega))
    cases hready with
    | leaf value =>
      have hz : depth = 0#usize := by scalar_tac
      subst depth
      have hhas' : update_map.HasValueAt mapInst updates start.val := by
        simpa only [hstartVal] using hguards rfl
      obtain ⟨pending, hpending⟩ := update_map.get_some_of_hasValueAt mapInst updates hhas'
      obtain ⟨cloned, hcloned⟩ := hclone.2 start pending (by omega)
        (by simp only [leafCapacity]; omega) hpending
      refine ⟨.Leaf { hash := Array.repeat 32#usize 0#u8, value := cloned }, ?_⟩
      simp only [Tree.with_updated_leaves, opt_hash_none, default_hash, bind_tc_ok,
        ↓reduceIte, hstart, hpending, core.option.OptionShared0T.cloned, hcloned,
        core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        Tree.leaf_with_hash, leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
    | packed factor value hnonempty hfit =>
      have hz : depth = 0#usize := by scalar_tac
      subst depth
      simp only [subtreeCapacity, leafCapacity, pow_zero, Nat.mul_one] at halign hoffset hend hwindow hcapacity
      obtain ⟨after, hafter, _⟩ := packed_leaf.PackedLeaf.update_success
        ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst mapInst value start factor
        (Array.repeat 32#usize 0#u8) updates newLength hlayout.tree_hash_packing_factor_eq
        (by rw [hstartVal, Nat.add_mod, halign, hoffset]; simp)
        (by omega) (by simpa only [hstartVal] using hwindow) hcapacity
        (fun query _ _ => hget query) hclone.1
        (fun query value hlo hhi hget => hclone.2 query value (by omega)
          (by simp only [leafCapacity]; omega) hget)
      refine ⟨.PackedLeaf after, ?_⟩
      simp only [Tree.with_updated_leaves, opt_hash_none, default_hash, bind_tc_ok,
        ↓reduceIte, hstart, hafter, core.result.Result.Insts.CoreOpsTry.branch,
        triomphe.arc.Arc.new]
    | @node factor oldHash left right child leftLength rightLength hleft hright hshape =>
      obtain ⟨nd, shift, stride, parentShift, width, subtreeEnd, lo, middle, stop,
        hnd, hndVal, hshift, hstride, hparentShift, hwidth, hsubtreeEnd, hlo, hmiddle, hstop,
        hrightPrefix, hloVal, hmiddleVal, hstopVal⟩ := Tree.bulk_update_node_arithmetic ValueInst
          hlayout depth prefix1 offset (by omega) (by simpa only [hdepth] using halign)
          (by simpa only [hdepth] using hend)
      have hndDepth : nd.val = child := by omega
      rw [hndDepth] at hrightPrefix hmiddleVal
      rw [hdepth] at hstopVal
      have hcap : subtreeCapacity factor (child + 1) = 2 * subtreeCapacity factor child := by
        simp only [subtreeCapacity, pow_succ]
        ring
      have hfull : 0 < rightLength → leftLength = subtreeCapacity factor child := by
        rcases hshape with ⟨_, hz⟩ | ⟨_, hfull⟩
        · omega
        · exact hfull
      have hwindow' := hwindow
      rw [hcap, Nat.mul_comm 2] at hwindow'
      obtain ⟨leftWindow, rightWindow⟩ := hwindow'.split hleft.length_le_capacity hfull
      have halignLeft : prefix1.val % subtreeCapacity factor child = 0 := by
        apply mod_half_eq_zero
        rwa [Nat.mul_comm, ← hcap]
      have halignRight : (prefix1 ||| stride).val % subtreeCapacity factor child = 0 := by
        rw [hrightPrefix, Nat.add_mod_right]
        exact halignLeft
      obtain ⟨bl, hbl⟩ := hqueries.left_query hloVal hmiddleVal
      obtain ⟨br, hbr⟩ := hqueries.right_query (hi := stop) hmiddleVal (by omega)
      have hguard := hguards lo middle stop hloVal hmiddleVal (by omega)
      have hsome : bl = true ∨ br = true := by
        cases bl with
        | true => exact Or.inl rfl
        | false =>
          cases br with
          | true => exact Or.inr rfl
          | false => exact False.elim (hguard.1 ⟨hbl, hbr⟩)
      have childSuccess : ∀ (old : Tree T) (start lo hi : Std.Usize) (oldLen newLen : Nat),
          DenseTree factor old child oldLen →
          start.val % subtreeCapacity factor child = 0 →
          start.val + offset.val + subtreeCapacity factor child ≤ Std.Usize.max →
          lo.val = start.val + offset.val →
          hi.val = start.val + offset.val + subtreeCapacity factor child →
          DenseUpdateWindow (update_map.HasValueAt mapInst updates)
            (start.val + offset.val) (subtreeCapacity factor child) oldLen newLen →
          newLen ≤ subtreeCapacity factor child →
          (mapInst.has_any_in_range updates lo hi = ok true →
            old.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
              mapInst updates factor child (start.val + offset.val)) →
          (mapInst.has_any_in_range updates lo hi = ok true →
            BulkRangeOn (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
              mapInst updates factor child (start.val + offset.val)) →
          (mapInst.has_any_in_range updates lo hi = ok true →
            BulkGuardsPass mapInst updates factor child (start.val + offset.val)) →
          mapInst.has_any_in_range updates lo hi = ok true →
          ∃ new, Tree.with_updated_leaves ValueInst mapInst old updates start offset nd none =
            ok (core.result.Result.Ok new) := by
        intro old start lo hi oldLen newLen hdense halign hend hlo hhi hwindow hcap hclones hscoped hdescend hanswer
        have hsmall : 2 * nd.val + zeroBit old < n := by
          have := zeroBit_le_one old
          simp only [zeroBit] at hmeasure
          omega
        exact ih _ hsmall nd child old start offset oldLen newLen (Nat.le_refl _)
          hndDepth (.ofDense hdense) halign hoffset hend hwindow hcap
          (hdescend hanswer) (hclones hanswer) (hscoped hanswer)
      have leftSuccess : bl = true → ∃ new,
          Tree.with_updated_leaves ValueInst mapInst left updates prefix1 offset nd none =
            ok (core.result.Result.Ok new) := by
        intro htrue
        apply childSuccess left prefix1 lo middle leftLength (min newLength (subtreeCapacity factor child))
          hleft halignLeft (by omega) hloVal hmiddleVal leftWindow (Nat.min_le_right _ _)
          (fun hselected => hclone.1 lo middle hloVal hmiddleVal hselected)
          (fun hselected => hqueries.left hloVal hmiddleVal hselected)
          hguard.2.1
        simpa only [htrue] using hbl
      have rightSuccess : br = true → ∃ new,
          Tree.with_updated_leaves ValueInst mapInst right updates (prefix1 ||| stride) offset nd none =
            ok (core.result.Result.Ok new) := by
        intro htrue
        apply childSuccess right (prefix1 ||| stride) middle stop rightLength
          (newLength - subtreeCapacity factor child) hright halignRight (by omega)
          (by omega) (by omega) ?_ (by omega) (fun hselected => by
            have h := hclone.2 middle stop hmiddleVal (by omega) hselected
            simpa only [hrightPrefix, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)
          (fun hselected => by
            have h := hqueries.right (hi := stop) hmiddleVal (by omega) hselected
            simpa only [hrightPrefix, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)
          (fun hselected => by
            have h := hguard.2.2 hselected
            simpa only [hrightPrefix, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)
          (by simpa only [htrue] using hbr)
        have heq : (prefix1 ||| stride).val + offset.val =
            (prefix1.val + offset.val) + subtreeCapacity factor child := by omega
        simpa only [heq] using rightWindow
      have hpositive : depth > 0#usize := by scalar_tac
      cases bl <;> cases br
      · simp at hsome
      · obtain ⟨newRight, hnewRight⟩ := rightSuccess rfl
        refine ⟨.Node (Array.repeat 32#usize 0#u8) left newRight, ?_⟩
        rw [Tree.with_updated_leaves]
        simp only [opt_hash_none, default_hash, bind_tc_ok, Bool.false_eq_true,
          hpositive, ↓reduceIte, hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq,
          lift, hnd, hshift, hstride, hparentShift, hwidth, hsubtreeEnd, hlo, hmiddle, hstop,
          hbl, hbr, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hnewRight,
          core.result.Result.Insts.CoreOpsTry.branch, Tree.node, lock_api.rwlock.RwLock.new,
          triomphe.arc.Arc.new]
      · obtain ⟨newLeft, hnewLeft⟩ := leftSuccess rfl
        refine ⟨.Node (Array.repeat 32#usize 0#u8) newLeft right, ?_⟩
        rw [Tree.with_updated_leaves]
        simp only [opt_hash_none, default_hash, bind_tc_ok, Bool.false_eq_true,
          hpositive, ↓reduceIte, hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq,
          lift, hnd, hshift, hstride, hparentShift, hwidth, hsubtreeEnd, hlo, hmiddle, hstop,
          hbl, hbr, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hnewLeft,
          core.result.Result.Insts.CoreOpsTry.branch, Tree.node, lock_api.rwlock.RwLock.new,
          triomphe.arc.Arc.new]
      · obtain ⟨newLeft, hnewLeft⟩ := leftSuccess rfl
        obtain ⟨newRight, hnewRight⟩ := rightSuccess rfl
        refine ⟨.Node (Array.repeat 32#usize 0#u8) newLeft newRight, ?_⟩
        rw [Tree.with_updated_leaves]
        simp only [opt_hash_none, default_hash, bind_tc_ok,
          hpositive, ↓reduceIte, hlayout.opt_packing_depth_eq, hlayout.unwrap_opt_packing_depth_eq,
          lift, hnd, hshift, hstride, hparentShift, hwidth, hsubtreeEnd, hlo, hmiddle, hstop,
          hbl, hbr, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref, hnewLeft, hnewRight,
          core.result.Result.Insts.CoreOpsTry.branch, Tree.node, lock_api.rwlock.RwLock.new,
          triomphe.arc.Arc.new]
    | zero factor zeroDepth =>
      have heq : zeroDepth = depth := by scalar_tac
      subst zeroDepth
      by_cases hz : depth = 0#usize
      · subst depth
        cases factor with
        | none =>
          have hhas' : update_map.HasValueAt mapInst updates start.val := by
            simpa only [hstartVal] using hguards rfl
          obtain ⟨pending, hpending⟩ := update_map.get_some_of_hasValueAt mapInst updates hhas'
          obtain ⟨cloned, hcloned⟩ := hclone.2 start pending (by omega)
            (by simp only [leafCapacity]; omega) hpending
          refine ⟨.Leaf { hash := Array.repeat 32#usize 0#u8, value := cloned }, ?_⟩
          simp only [Tree.with_updated_leaves, opt_hash_none, default_hash, bind_tc_ok,
            ↓reduceIte, hlayout.opt_packing_factor_eq, core.option.Option.is_some,
            Option.isSome, Bool.false_eq_true, hstart, hpending, core.option.OptionShared0T.cloned,
            hcloned, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
            Tree.leaf_with_hash, leaf.Leaf.with_hash, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.new]
        | some factor =>
          let empty : packed_leaf.PackedLeaf T :=
            { hash := Array.repeat 32#usize 0#u8, values := alloc.vec.Vec.new T }
          simp only [subtreeCapacity, leafCapacity, show (0#usize).val = 0 from rfl, pow_zero, Nat.mul_one]
            at halign hoffset hend hwindow hcapacity
          obtain ⟨after, hafter, _⟩ := packed_leaf.PackedLeaf.update_success
            ValueInst.tree_hashTreeHashInst ValueInst.corecloneCloneInst mapInst empty start factor
            (Array.repeat 32#usize 0#u8) updates newLength hlayout.tree_hash_packing_factor_eq
            (by rw [hstartVal, Nat.add_mod, halign, hoffset]; simp)
            (by omega) (by simpa only [empty, alloc.vec.Vec.new, hstartVal,
              _root_.List.length_nil] using hwindow) hcapacity
            (fun query _ _ => hget query)
            (by intro value hv; simp [empty] at hv)
            (fun query value hlo hhi hget => hclone.2 query value (by omega)
              (by simp only [leafCapacity]; omega) hget)
          refine ⟨.PackedLeaf after, ?_⟩
          simp only [Tree.with_updated_leaves, opt_hash_none, default_hash, bind_tc_ok,
            ↓reduceIte, hlayout.opt_packing_factor_eq, core.option.Option.is_some, Option.isSome,
            packed_leaf.PackedLeaf.empty, alloy_primitives.bits.fixed.FixedBytes.ZERO,
            lock_api.rwlock.RwLock.new, hlayout.tree_hash_packing_factor_eq, hstart,
            alloc.vec.Vec.with_capacity]
          change (packed_leaf.PackedLeaf.update ValueInst.tree_hashTreeHashInst
            ValueInst.corecloneCloneInst mapInst empty start (Array.repeat 32#usize 0#u8) updates >>= _) = _
          simp only [hafter, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, triomphe.arc.Arc.new]
      · obtain ⟨nd, hnd, hndVal⟩ := usize_sub_one_succeeds (by scalar_tac : 0 < depth.val)
        have hsmall : 2 * depth.val + zeroBit
            (Tree.Node (Array.repeat 32#usize 0#u8) (.Zero nd) (.Zero nd) : Tree T) < n := by
          simp only [zeroBit] at hmeasure ⊢
          omega
        have hready : UpdateReady factor
            (Tree.Node (Array.repeat 32#usize 0#u8) (.Zero nd) (.Zero nd) : Tree T) depth.val 0 := by
          rw [hndVal]
          exact .node factor _ (.Zero nd) (.Zero nd) nd.val 0 0
            (.zero factor nd) (.zero factor nd) (Or.inl ⟨rfl, rfl⟩)
        have hcloneExpanded :
            (Tree.Node (Array.repeat 32#usize 0#u8) (.Zero nd) (.Zero nd) : Tree T).BulkCloneOn
              (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
              mapInst updates factor depth.val (prefix1.val + offset.val) := by
          rw [hndVal] at hclone ⊢
          exact (Tree.BulkCloneOn.zero_expand _ mapInst updates factor depth nd nd.val _ _).mp hclone
        obtain ⟨after, hafter⟩ := ih _ hsmall depth depth.val _ prefix1 offset 0 newLength
          (Nat.le_refl _) rfl hready halign hoffset hend hwindow hcapacity hguards hcloneExpanded hqueries
        refine ⟨after, ?_⟩
        rw [Tree.with_updated_leaves]
        simp only [opt_hash_none, default_hash, bind_tc_ok, hz, ↓reduceIte, hnd,
          Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreCloneClone.clone,
          Tree.node, lock_api.rwlock.RwLock.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref]
        exact hafter

/-- Dense binary rebuilding succeeds when the actual selected missing-update
guards pass. No range-correctness law or pending-value witness at internal
nodes is required. Clone and range-query termination remain scoped to the
selected input; the dense update window supplies packed insertion bounds. -/
theorem Tree.with_updated_leaves_success_of_guards {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (before : Tree T) (prefix1 offset depth : Std.Usize) (oldLength newLength : Nat)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hqueries : BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hcapacity : newLength ≤ subtreeCapacity factor depth.val)
    (hguards : BulkGuardsPass mapInst updates factor depth.val (prefix1.val + offset.val)) :
    ∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth none = ok (core.result.Result.Ok after) := by
  exact bulk_update_success_aux ValueInst mapInst updates hlayout hget
    _ depth depth.val before prefix1 offset oldLength newLength (Nat.le_refl _) rfl
    (.ofDense hdense) halign hoffset hend hwindow hcapacity hguards hclone hqueries

/-- Compatibility contract using pending-value activation and range reflection. -/
theorem Tree.with_updated_leaves_success_of_enabled {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (before : Tree T) (prefix1 offset depth : Std.Usize) (oldLength newLength : Nat)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hqueries : BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hcapacity : newLength ≤ subtreeCapacity factor depth.val)
    (hhas : BulkUpdateEnabled mapInst updates factor depth.val (prefix1.val + offset.val)) :
    ∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth none = ok (core.result.Result.Ok after) := by
  exact Tree.with_updated_leaves_success_of_guards ValueInst mapInst updates hlayout hget
    before prefix1 offset depth oldLength newLength hclone hqueries hdense halign hoffset hend
    hwindow hcapacity (BulkGuardsPass.of_enabled hhas hrange)

/-- A dense subtree with a nonempty dense update window can be rebuilt by
the actual bulk recursion. Its endpoint supplies all shift, arithmetic, and
vector bounds. External cloning need only terminate; identity is unnecessary
for successful execution. This is the no-precomputed-hashes path used by
`ProgressiveList.apply_updates`. -/
theorem Tree.with_updated_leaves_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (before : Tree T) (prefix1 offset depth : Std.Usize) (oldLength newLength : Nat)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hqueries : BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hcapacity : newLength ≤ subtreeCapacity factor depth.val)
    (hhas : ∃ index, index < subtreeCapacity factor depth.val ∧
      update_map.HasValueAt mapInst updates (prefix1.val + offset.val + index)) :
    ∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth none = ok (core.result.Result.Ok after) := by
  exact Tree.with_updated_leaves_success_of_enabled ValueInst mapInst updates hlayout hget
    before prefix1 offset depth oldLength newLength hclone hqueries hrange hdense
    halign hoffset hend hwindow hcapacity (Or.inr hhas)

/-- Total bulk reconstruction preserves density at exactly the new window
length. The nonempty update witness supplies positivity, so callers need not
assume a separate positive-result invariant. -/
theorem Tree.with_updated_leaves_total_dense {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (before : Tree T) (prefix1 offset depth : Std.Usize) (oldLength newLength : Nat)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hqueries : BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hcapacity : newLength ≤ subtreeCapacity factor depth.val)
    (hhas : ∃ index, index < subtreeCapacity factor depth.val ∧
      update_map.HasValueAt mapInst updates (prefix1.val + offset.val + index)) :
    ∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth none = ok (core.result.Result.Ok after) ∧
      DenseTree factor after depth.val newLength := by
  obtain ⟨after, hafter⟩ := Tree.with_updated_leaves_success ValueInst mapInst updates
    hlayout hget before prefix1 offset depth oldLength newLength
    hclone hqueries hrange hdense halign hoffset hend hwindow hcapacity hhas
  exact ⟨after, hafter, (Tree.with_updated_leaves_capacity_dense ValueInst mapInst updates
    hlayout hrange hdense halign hoffset hwindow (hwindow.length_pos_of_update hhas)
    hcapacity hafter).2⟩

/-- Total binary bulk update has exactly the merged pending/backing contents
and the new dense length. No successful recursive call is a premise. -/
theorem Tree.with_updated_leaves_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (before : Tree T) (prefix1 offset depth : Std.Usize) (oldLength newLength : Nat)
    (hclone : before.BulkCloneLaws ValueInst.corecloneCloneInst
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hqueries : BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hcapacity : newLength ≤ subtreeCapacity factor depth.val)
    (hhas : ∃ index, index < subtreeCapacity factor depth.val ∧
      update_map.HasValueAt mapInst updates (prefix1.val + offset.val + index)) :
    ∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth none = ok (core.result.Result.Ok after) ∧
      DenseTree factor after depth.val newLength ∧
      Tree.BulkContents mapInst updates factor before after depth.val prefix1.val offset.val := by
  obtain ⟨after, hafter, hdenseAfter⟩ := Tree.with_updated_leaves_total_dense ValueInst mapInst updates
    hlayout hget before prefix1 offset depth oldLength newLength
    hclone.terminates hqueries hrange
    hdense halign hoffset hend hwindow hcapacity hhas
  exact ⟨after, hafter, hdenseAfter,
    (Tree.with_updated_leaves_capacity_shape_contents ValueInst mapInst updates
      hlayout hclone.preserves hrange.excludesValues hdense.shape halign hoffset hafter).2.2⟩

/-- Under the remaining execution laws and dense input/window invariants,
the binary start condition is necessary and sufficient for actual success.
No successful update or pending-value witness is assumed upfront. -/
theorem Tree.with_updated_leaves_success_iff_enabled {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (before : Tree T) (prefix1 offset depth : Std.Usize) (oldLength newLength : Nat)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hqueries : BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hrange : BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hcapacity : newLength ≤ subtreeCapacity factor depth.val) :
    (∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
      prefix1 offset depth none = ok (core.result.Result.Ok after)) ↔
      BulkUpdateEnabled mapInst updates factor depth.val (prefix1.val + offset.val) := by
  constructor
  · rintro ⟨after, hupdate⟩
    apply Tree.with_updated_leaves_enabled ValueInst mapInst hlayout ?_ halign
      hrange.selectsValues hupdate
    intro leaf hleaf
    have hshape := hdense.shape
    rw [hleaf] at hshape
    generalize depth.val = treeDepth at hshape
    cases hshape
    simp
  · intro henabled
    exact Tree.with_updated_leaves_success_of_enabled ValueInst mapInst updates hlayout hget
      before prefix1 offset depth oldLength newLength hclone hqueries hrange hdense
      halign hoffset hend hwindow hcapacity henabled


/-- Under the remaining input, arithmetic, lookup, and clone/query-termination
conditions, successful binary rebuilding is equivalent to passing the selected
missing-update guards. Neither direction assumes range correctness. -/
theorem Tree.with_updated_leaves_success_iff_guards {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (before : Tree T) (prefix1 offset depth : Std.Usize) (oldLength newLength : Nat)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hqueries : BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      mapInst updates factor depth.val (prefix1.val + offset.val))
    (hdense : DenseTree factor before depth.val oldLength)
    (halign : prefix1.val % subtreeCapacity factor depth.val = 0)
    (hoffset : offset.val % leafCapacity factor = 0)
    (hend : prefix1.val + offset.val + subtreeCapacity factor depth.val ≤ Std.Usize.max)
    (hwindow : DenseUpdateWindow (update_map.HasValueAt mapInst updates)
      (prefix1.val + offset.val) (subtreeCapacity factor depth.val) oldLength newLength)
    (hcapacity : newLength ≤ subtreeCapacity factor depth.val)
    : (∃ after, Tree.with_updated_leaves ValueInst mapInst before updates
        prefix1 offset depth none = ok (core.result.Result.Ok after)) ↔
      BulkGuardsPass mapInst updates factor depth.val (prefix1.val + offset.val) := by
  constructor
  · rintro ⟨after, hupdate⟩
    exact Tree.with_updated_leaves_guards_pass ValueInst mapInst hlayout hdense.shape halign hupdate
  · intro hguards
    exact Tree.with_updated_leaves_success_of_guards ValueInst mapInst updates hlayout hget
      before prefix1 offset depth oldLength newLength hclone hqueries hdense halign hoffset hend
      hwindow hcapacity hguards

end milhouse.tree
