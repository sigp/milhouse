import Tree.BulkUpdate.Success
import Tree.ProgressiveTree.BulkUpdate.Density
import Tree.ProgressiveTree.BulkUpdate.CloneScope
import Tree.ProgressiveTree.BulkUpdate.RangeScope
import Tree.ProgressiveTree.BulkUpdate.Activation
import Tree.ProgressiveTree.LengthFits

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

private def finishNode {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (next : Std.U32) (stop : Std.Usize)
    (left : tree.Tree T) (right : ProgressiveTree T) :
    Result (core.result.Result (ProgressiveTree T) error.Error) := do
  let b ← core.option.Option.is_some_and
    (ProgressiveTree.with_updated_leaves_recursive.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool
      ValueInst mapInst) maximum stop
  if b then
    let r ← ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst right updates maximum next
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue newRight =>
      ok (.Ok (.ProgressiveNode (Array.repeat 32#usize 0#u8) left newRight))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (ProgressiveTree T) (core.convert.FromSame error.Error) residual
  else ok (.Ok (.ProgressiveNode (Array.repeat 32#usize 0#u8) left right))

private theorem finishNode_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (maximum : Option Std.Usize) (next : Std.U32) (stop : Std.Usize)
    (left : tree.Tree T) (right : ProgressiveTree T)
    (hrecursive : (∃ last, maximum = some last ∧ stop.val ≤ last.val) →
      ∃ result, ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst right updates maximum next =
        ok (core.result.Result.Ok result)) :
    ∃ result, finishNode ValueInst mapInst updates maximum next stop left right =
      ok (core.result.Result.Ok result) := by
  cases maximum with
  | none =>
    exact ⟨.ProgressiveNode (Array.repeat 32#usize 0#u8) left right, rfl⟩
  | some last =>
    by_cases hge : stop ≤ last
    · obtain ⟨result, hresult⟩ := hrecursive ⟨last, rfl, hge⟩
      refine ⟨.ProgressiveNode (Array.repeat 32#usize 0#u8) left result, ?_⟩
      simp only [finishNode, core.option.Option.is_some_and,
        ProgressiveTree.with_updated_leaves_recursive.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once,
        bind_tc_ok, ge_iff_le, hge, decide_true, ↓reduceIte, hresult,
        core.result.Result.Insts.CoreOpsTry.branch]
    · refine ⟨.ProgressiveNode (Array.repeat 32#usize 0#u8) left right, ?_⟩
      simp only [finishNode, core.option.Option.is_some_and,
        ProgressiveTree.with_updated_leaves_recursive.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once,
        bind_tc_ok, ge_iff_le, hge, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem bulk_update_success_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (maximum : Option Std.Usize) (oldLength newLength : Nat)
    (hmaximum : ∀ last, maximum = some last → last.val < newLength)
    (hdomain : DenseUpdateDomain oldLength newLength (update_map.HasValueAt mapInst updates))
    (hfits : ProgressiveTree.LengthFits factor newLength) :
    ∀ (fuel : Nat) (depth : Std.U32) (before : ProgressiveTree T),
      Std.U32.max - depth.val ≤ fuel →
      subtreeCapacity factor (2 * depth.val) ≤ Std.Usize.max →
      before.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val) →
      before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
        ValueInst mapInst updates factor maximum depth →
      before.BulkRangeOn (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
        ValueInst mapInst updates factor maximum depth →
      before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
        ValueInst mapInst updates factor maximum depth →
      ∃ after, ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
        ok (core.result.Result.Ok after) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro depth before hfuel hcapacity hdense hclone hqueries hrange
    have hcapBits : subtreeCapacity factor (2 * depth.val) < 2 ^ System.Platform.numBits := by scalar_tac
    obtain ⟨next, binary, hnext, hbinary, hbinaryVal, _⟩ := next_layer_bounds ValueInst hlayout depth hcapBits
    have hnextVal : next.val = depth.val + 1 := by
      have hadd := UScalar.add_equiv depth 1#u32
      rw [hnext] at hadd
      simp at hadd
      omega
    obtain ⟨start, stop, hstart, hstop, hstartVal, hwidth, hoffset⟩ :=
      ProgressiveTree.layer_window ValueInst hlayout hnext hbinary (by simpa only [hbinaryVal] using hcapBits)
    have hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary :=
      ⟨hstart, hnext, hstop, hbinary⟩
    have hstopVal : stop.val = progressiveCapacity factor next.val := by
      rw [hnextVal, progressiveCapacity_succ, ← hstartVal, ← hbinaryVal]
      exact hwidth
    have hnonempty : start < stop := by
      have := hlayout.subtreeCapacity_pos binary.val
      change start.val < stop.val
      omega
    obtain ⟨has, hhas⟩ := hqueries.here hgeometry hnonempty
    have hhas' : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has := by
      simp only [ProgressiveTree.has_updates_in_range, hnonempty, ↓reduceIte, hhas]
    have updateLeft : ∀ left : tree.Tree T,
        DenseTree factor left (2 * depth.val)
          (min (oldLength - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val))) →
        has = true →
        left.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
          mapInst updates factor binary.val start.val →
        ∃ after, tree.Tree.with_updated_leaves ValueInst mapInst left updates 0#usize start binary none =
          ok (core.result.Result.Ok after) := by
      intro left hdenseLeft htrue hclones
      have hwindow := hdomain.window start.val (subtreeCapacity factor binary.val)
      apply tree.Tree.with_updated_leaves_success ValueInst mapInst updates hlayout hget
        left 0#usize start binary
        (min (oldLength - start.val) (subtreeCapacity factor binary.val))
        (min (newLength - start.val) (subtreeCapacity factor binary.val))
        (by simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using hclones)
        (by simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using
          hqueries.binary hgeometry (by simpa only [htrue] using hhas'))
        (by simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using
          hrange.binary hgeometry (by simpa only [htrue] using hhas'))
        (by simpa only [hstartVal, hbinaryVal] using hdenseLeft)
        (by simp) hoffset (by have := stop.hBounds; scalar_tac)
        (by simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using hwindow)
        (Nat.min_le_right _ _)
      obtain ⟨query, hlo, hhi, hhas⟩ := ((hrange.here hgeometry hnonempty) has hhas).mp htrue
      refine ⟨query - start.val, by omega, ?_⟩
      have heq : (0#usize).val + start.val + (query - start.val) = query := by
        change 0 + start.val + (query - start.val) = query
        omega
      rwa [heq]
    have finish : ∀ (left : tree.Tree T) (right : ProgressiveTree T),
        right.Dense factor next.val (oldLength - progressiveCapacity factor next.val) →
        ((∃ last, maximum = some last ∧ stop.val ≤ last.val) →
          right.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
            ValueInst mapInst updates factor maximum next) →
        ((∃ last, maximum = some last ∧ stop.val ≤ last.val) →
          right.BulkRangeOn (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
            ValueInst mapInst updates factor maximum next) →
        ((∃ last, maximum = some last ∧ stop.val ≤ last.val) →
          right.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
            ValueInst mapInst updates factor maximum next) →
        ∃ result, finishNode ValueInst mapInst updates maximum next stop left right =
          ok (core.result.Result.Ok result) := by
      intro left right hdenseRight hclones hscoped hranges
      apply finishNode_success ValueInst mapInst updates maximum next stop left right
      rintro ⟨last, hlast, hlastLo⟩
      have hlastHi := hmaximum last hlast
      have hnextFits := hfits next.val (by omega)
      have hless : Std.U32.max - next.val < fuel := by scalar_tac
      exact ih _ hless next right (Nat.le_refl _) hnextFits hdenseRight
        (hclones ⟨last, hlast, hlastLo⟩) (hscoped ⟨last, hlast, hlastLo⟩)
        (hranges ⟨last, hlast, hlastLo⟩)
    cases before with
    | ProgressiveZero =>
      cases has with
      | false =>
        refine ⟨.ProgressiveZero, ?_⟩
        rw [ProgressiveTree.with_updated_leaves_recursive]
        simp only [hstart, hnext, hstop, hbinary, hhas', bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
      | true =>
        have hold : oldLength ≤ progressiveCapacity factor depth.val := by
          have hlength := hdense.elements_length
          simp only [ProgressiveTree.elements, _root_.List.length_nil] at hlength
          omega
        have hzeroLeft : DenseTree factor (.Zero binary : tree.Tree T) (2 * depth.val)
            (min (oldLength - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val))) := by
          rw [Nat.sub_eq_zero_of_le hold, Nat.zero_min, ← hbinaryVal]
          exact .zero factor binary
        have hzeroRight : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).Dense factor next.val
            (oldLength - progressiveCapacity factor next.val) := by
          have hmono := progressiveCapacity_mono factor (show depth.val ≤ next.val by omega)
          rw [Nat.sub_eq_zero_of_le (by omega : oldLength ≤ progressiveCapacity factor next.val)]
          exact .zero factor next.val
        obtain ⟨newLeft, hnewLeft⟩ := updateLeft (.Zero binary) hzeroLeft rfl
          (hclone.zero_left hgeometry hhas')
        obtain ⟨result, hresult⟩ := finish newLeft .ProgressiveZero hzeroRight
          (hclone.zero_right hgeometry hhas') (hqueries.zero_right hgeometry hhas')
          (hrange.zero_right hgeometry hhas')
        refine ⟨result, ?_⟩
        rw [ProgressiveTree.with_updated_leaves_recursive]
        simp only [hstart, hnext, hstop, hbinary, hhas', bind_tc_ok, ↓reduceIte,
          tree.Tree.zero, triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          hnewLeft, core.result.Result.Insts.CoreOpsTry.branch,
          alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new]
        exact hresult
    | ProgressiveNode hash left right =>
      have hdenseRight : right.Dense factor next.val (oldLength - progressiveCapacity factor next.val) := by
        simpa only [hnextVal] using hdense.right_remainder
      have hrightClones := hclone.node_right hgeometry ⟨has, hhas'⟩
      have hrightQueries := hqueries.node_right hgeometry ⟨has, hhas'⟩
      have hrightRanges := hrange.node_right hgeometry ⟨has, hhas'⟩
      cases has with
      | false =>
        obtain ⟨result, hresult⟩ := finish left right hdenseRight hrightClones hrightQueries hrightRanges
        refine ⟨result, ?_⟩
        rw [ProgressiveTree.with_updated_leaves_recursive]
        simp only [hstart, hnext, hstop, hbinary, hhas', bind_tc_ok,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone, Bool.false_eq_true, ↓reduceIte,
          triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          core.result.Result.Insts.CoreOpsTry.branch,
          alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new]
        exact hresult
      | true =>
        obtain ⟨newLeft, hnewLeft⟩ := updateLeft left hdense.split_layer.1 rfl
          (hclone.node_left hgeometry hhas')
        obtain ⟨result, hresult⟩ := finish newLeft right hdenseRight hrightClones hrightQueries hrightRanges
        refine ⟨result, ?_⟩
        rw [ProgressiveTree.with_updated_leaves_recursive]
        simp only [hstart, hnext, hstop, hbinary, hhas', bind_tc_ok,
          triomphe.arc.Arc.Insts.CoreCloneClone.clone, ↓reduceIte,
          triomphe.arc.Arc.new, triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref,
          hnewLeft, core.result.Result.Insts.CoreOpsTry.branch,
          alloy_primitives.bits.fixed.FixedBytes.ZERO, lock_api.rwlock.RwLock.new]
        exact hresult

/-- Progressive bulk recursion terminates when the current layer fits and
every later occupied layer fits the final length. The maximum need only lie
below that length; it need not be attained by an update for termination. -/
theorem ProgressiveTree.with_updated_leaves_recursive_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (maximum : Option Std.Usize) (oldLength newLength : Nat)
    (hmaximum : ∀ last, maximum = some last → last.val < newLength)
    (hdomain : DenseUpdateDomain oldLength newLength (update_map.HasValueAt mapInst updates))
    (hfits : ProgressiveTree.LengthFits factor newLength)
    (depth : Std.U32) (before : ProgressiveTree T)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      ValueInst mapInst updates factor maximum depth)
    (hqueries : before.BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      ValueInst mapInst updates factor maximum depth)
    (hrange : before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum depth)
    (hcapacity : subtreeCapacity factor (2 * depth.val) ≤ Std.Usize.max)
    (hdense : before.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val)) :
    ∃ after, ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (core.result.Result.Ok after) := by
  exact bulk_update_success_aux ValueInst mapInst updates hlayout hget
    maximum oldLength newLength hmaximum hdomain hfits _ depth before
    (Nat.le_refl _) hcapacity hdense hclone hqueries hrange

/-- The public progressive bulk update succeeds from the dense update domain
and capacities of occupied final layers. Its empty root has a representable
initial layer directly from packing layout, without a nonempty-list premise. -/
theorem ProgressiveTree.with_updated_leaves_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hget : ∀ query, ∃ found, mapInst.get updates query = ok found)
    (maximum : Option Std.Usize) (hmax : mapInst.max_index updates = ok maximum)
    (oldLength newLength : Nat)
    (hmaximum : ∀ last, maximum = some last → last.val < newLength)
    (hdomain : DenseUpdateDomain oldLength newLength (update_map.HasValueAt mapInst updates))
    (hfits : ProgressiveTree.LengthFits factor newLength)
    (before : ProgressiveTree T)
    (hclone : before.BulkCloneOn (fun value => ∃ cloned, ValueInst.corecloneCloneInst.clone value = ok cloned)
      ValueInst mapInst updates factor maximum 0#u32)
    (hqueries : before.BulkRangeOn
      (fun lo hi => ∃ answer, mapInst.has_any_in_range updates lo hi = ok answer)
      ValueInst mapInst updates factor maximum 0#u32)
    (hrange : before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum 0#u32)
    (hdense : before.Dense factor 0 oldLength) :
    ∃ after, ProgressiveTree.with_updated_leaves ValueInst mapInst before updates =
      ok (core.result.Result.Ok after) := by
  have hroot : subtreeCapacity factor (2 * (0#u32).val) ≤ Std.Usize.max := by
    cases factor <;> simp only [subtreeCapacity, leafCapacity,
      show (0#u32).val = 0 from rfl, Nat.mul_zero, pow_zero, Nat.mul_one] <;> scalar_tac
  obtain ⟨after, hafter⟩ := ProgressiveTree.with_updated_leaves_recursive_success ValueInst mapInst updates
    hlayout hget maximum oldLength newLength hmaximum hdomain hfits
    0#u32 before hclone hqueries hrange hroot (by simpa only [show (0#u32).val = 0 from rfl,
      progressiveCapacity_zero, Nat.sub_zero] using hdense)
  exact ⟨after, by simp only [ProgressiveTree.with_updated_leaves, hmax, bind_tc_ok, hafter]⟩

end milhouse.progressive_tree
