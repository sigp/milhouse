import Tree.BulkUpdate.Density
import Tree.ProgressiveTree.BulkUpdate.Range
import Tree.ProgressiveTree.BulkUpdate.Steps
import Tree.ProgressiveTree.BulkUpdate.RangeScope
import Tree.ProgressiveTree.Iter.Layer

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Updating a selected progressive layer preserves its exact dense prefix.
    Its global offset and binary capacity are derived from actual execution,
    including the positive range answer that triggered the update. -/
theorem ProgressiveTree.updated_layer_dense {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {depth next : Std.U32} {start stop binary : Std.Usize} {before after : tree.Tree T}
    (hlocal : update_map.RangeReflectsValuesAt mapInst updates start stop)
    (hrange : tree.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      mapInst updates factor binary.val start.val)
    {oldLength newLength : Nat}
    (hdomain : DenseUpdateDomain oldLength newLength (update_map.HasValueAt mapInst updates))
    (hnext : depth + 1#u32 = ok next)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hhas : ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok true)
    (hdense : DenseTree factor before (2 * depth.val)
      (min (oldLength - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val))))
    (hupdate : tree.Tree.with_updated_leaves ValueInst mapInst before updates
      0#usize start binary none = ok (core.result.Result.Ok after)) :
    subtreeCapacity factor (2 * depth.val) < 2 ^ System.Platform.numBits ∧
      DenseTree factor after (2 * depth.val)
        (min (newLength - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val))) := by
  obtain ⟨hnonempty, hmap⟩ := ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas
  have hstartVal := ProgressiveTree.total_capacity_unclamped ValueInst
    hlayout.opt_packing_factor_eq hstart (by scalar_tac)
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  have hoffset : start.val % leafCapacity factor = 0 := by
    rw [hstartVal]
    exact progressiveCapacity_aligned factor depth.val
  have hwindow := hdomain.window start.val (subtreeCapacity factor binary.val)
  obtain ⟨index, hlo, _, hindex⟩ := (hlocal true hmap).mp rfl
  have hbound := hdomain.updates_bounded index hindex
  have hpositive : 0 < min (newLength - start.val) (subtreeCapacity factor binary.val) := by
    have := hlayout.subtreeCapacity_pos binary.val
    omega
  have hdense' : DenseTree factor before binary.val
      (min (oldLength - start.val) (subtreeCapacity factor binary.val)) := by
    simpa only [hstartVal, hbinaryVal] using hdense
  have hresult := tree.Tree.with_updated_leaves_capacity_dense ValueInst mapInst updates hlayout
    (by simpa only [show (0#usize).val = 0 from rfl, Nat.zero_add] using hrange) hdense' (by simp) hoffset (by simpa using hwindow) hpositive (Nat.min_le_right _ _) hupdate
  simpa only [hstartVal, hbinaryVal] using hresult

private theorem bulk_dense_aux {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {oldLength : Nat} {newLength : Std.Usize}
    (hextent : newLength.val ≤ maximum.elim oldLength (fun last => max (last.val + 1) oldLength))
    (hdomain : DenseUpdateDomain oldLength newLength.val (update_map.HasValueAt mapInst updates)) :
    ∀ (fuel : Nat) (depth : Std.U32) (before after : ProgressiveTree T),
      Std.U32.max - depth.val ≤ fuel →
      before.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val) →
      before.Fits factor depth.val →
      before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
        ValueInst mapInst updates factor maximum depth →
      ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
        ok (core.result.Result.Ok after) →
      after.Dense factor depth.val (newLength.val - progressiveCapacity factor depth.val) ∧
        after.Fits factor depth.val := by
  have hcomplete := update_map.extensionComplete_of_denseUpdateDomain mapInst updates hdomain
  have hmono := hdomain.length_mono
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro depth before after hfuel hdense hfit hrange hupdate
    obtain ⟨start, next, stop, binary, hstart, hnext, hstop, hbinary, hstep⟩ :=
      ProgressiveTree.with_updated_leaves_recursive_step ValueInst mapInst hupdate
    have hgeometry : ProgressiveTree.BulkLayerGeometry ValueInst depth next start stop binary :=
      ⟨hstart, hnext, hstop, hbinary⟩
    have hadd := UScalar.add_equiv depth 1#u32
    rw [hnext] at hadd
    simp at hadd
    have hnextVal : next.val = depth.val + 1 := by omega
    have hless : Std.U32.max - next.val < fuel := by scalar_tac
    have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
    obtain ⟨actualStop, hactualStop, hstopVal⟩ :=
      ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq next
    rw [hstop] at hactualStop
    cases hactualStop
    have hstopLe : stop.val ≤ progressiveCapacity factor next.val := by omega
    have rightCorrect : ∀ right newRight : ProgressiveTree T,
        right.Dense factor next.val (oldLength - progressiveCapacity factor next.val) →
        right.Fits factor next.val →
        ((∃ last, maximum = some last ∧ stop.val ≤ last.val) →
          right.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
            ValueInst mapInst updates factor maximum next) →
        ProgressiveTree.BulkRightStep ValueInst mapInst updates maximum next stop right newRight →
        newRight.Dense factor next.val (newLength.val - progressiveCapacity factor next.val) ∧
          newRight.Fits factor next.val := by
      intro right newRight hdense hfit hranges hright
      rcases hright with ⟨hbefore, rfl⟩ | ⟨hselected, hrecursive⟩
      · have hlength : newLength.val ≤ max oldLength stop.val := by
          cases maximum with
          | none => simp only [Option.elim_none] at hextent; omega
          | some last =>
            have hlast := hbefore last rfl
            simp only [Option.elim_some] at hextent
            omega
        have heq : newLength.val - progressiveCapacity factor next.val =
            oldLength - progressiveCapacity factor next.val := by omega
        exact ⟨heq ▸ hdense, hfit⟩
      · exact ih _ hless next right newRight (Nat.le_refl _) hdense hfit (hranges hselected) hrecursive
    have finishNode : ∀ hash (left : tree.Tree T) (right : ProgressiveTree T),
        DenseTree factor left (2 * depth.val)
          (min (newLength.val - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val))) →
        subtreeCapacity factor (2 * depth.val) < 2 ^ System.Platform.numBits →
        right.Dense factor next.val (newLength.val - progressiveCapacity factor next.val) →
        right.Fits factor next.val →
        (ProgressiveTree.ProgressiveNode hash left right).Dense factor depth.val
          (newLength.val - progressiveCapacity factor depth.val) ∧
          (ProgressiveTree.ProgressiveNode hash left right).Fits factor depth.val := by
      intro hash left right hleft hleftFit hright hrightFit
      have hremaining : newLength.val - progressiveCapacity factor next.val =
          (newLength.val - progressiveCapacity factor depth.val) - subtreeCapacity factor (2 * depth.val) := by
        rw [hnextVal, progressiveCapacity_succ, Nat.sub_sub]
      have hsum : newLength.val - progressiveCapacity factor depth.val =
          min (newLength.val - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val)) +
            (newLength.val - progressiveCapacity factor next.val) := by omega
      refine ⟨?_, hleftFit, by simpa only [hnextVal] using hrightFit⟩
      rw [hsum]
      exact .node hash hleft (by simpa only [hnextVal] using hright) (by omega)
    cases hstep with
    | zero hempty =>
      have hold : oldLength ≤ progressiveCapacity factor depth.val := by
        have hlength := hdense.elements_length
        simp only [ProgressiveTree.elements, List.length_nil] at hlength
        omega
      have hlength := ProgressiveTree.length_le_of_empty_zero_layer ValueInst mapInst hlayout
        (hrange.excludesValues.here hgeometry) hcomplete hnext hstart hstop hold hempty
      have hz : newLength.val - progressiveCapacity factor depth.val = 0 := by omega
      rw [hz]
      exact ⟨.zero factor depth.val, trivial⟩
    | @expand right newLeft hash hhas hleft hright =>
      have hold : oldLength ≤ progressiveCapacity factor depth.val := by
        have hlength := hdense.elements_length
        simp only [ProgressiveTree.elements, List.length_nil] at hlength
        omega
      have hzeroLeft : DenseTree factor (.Zero binary : tree.Tree T) (2 * depth.val)
          (min (oldLength - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val))) := by
        have hz : oldLength - progressiveCapacity factor depth.val = 0 := by omega
        rw [hz, Nat.zero_min, ← hbinaryVal]
        exact .zero factor binary
      obtain ⟨hleftFit, hleftDense⟩ := ProgressiveTree.updated_layer_dense ValueInst mapInst updates
        hlayout (hrange.here hgeometry (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1)
          (hrange.binary hgeometry hhas) hdomain hnext hstart hbinary hhas hzeroLeft hleft
      have hrightDense : (ProgressiveTree.ProgressiveZero : ProgressiveTree T).Dense factor next.val
          (oldLength - progressiveCapacity factor next.val) := by
        have hle := progressiveCapacity_mono factor (show depth.val ≤ next.val by omega)
        have hz : oldLength - progressiveCapacity factor next.val = 0 := by omega
        rw [hz]
        exact .zero factor next.val
      obtain ⟨hrightDense, hrightFit⟩ := rightCorrect .ProgressiveZero right hrightDense trivial
        (hrange.zero_right hgeometry hhas) hright
      exact finishNode hash newLeft right hleftDense hleftFit hrightDense hrightFit
    | @node left newLeft right newRight oldHash newHash hleft hright =>
      obtain ⟨holdLeft, _⟩ := hdense.split_layer
      have holdRight := hdense.right_remainder
      obtain ⟨hleftFit, hrightFit⟩ := hfit
      have hhasSuccess : ∃ has,
          ProgressiveTree.has_updates_in_range ValueInst mapInst updates start stop = ok has :=
        hleft.elim (fun h => ⟨false, h.1⟩) (fun h => ⟨true, h.1⟩)
      obtain ⟨hnewRight, hnewRightFit⟩ := rightCorrect right newRight
        (by simpa only [hnextVal] using holdRight) (by simpa only [hnextVal] using hrightFit)
        (hrange.node_right hgeometry hhasSuccess) hright
      have leftCorrect : DenseTree factor newLeft (2 * depth.val)
          (min (newLength.val - progressiveCapacity factor depth.val) (subtreeCapacity factor (2 * depth.val))) ∧
          subtreeCapacity factor (2 * depth.val) < 2 ^ System.Platform.numBits := by
        rcases hleft with ⟨hempty, rfl⟩ | ⟨hhas, hupdate⟩
        · obtain ⟨actualStart, actualStop, hactualStart, hactualStop, hstartExact, hwidth, _⟩ :=
            ProgressiveTree.layer_window ValueInst hlayout hnext hbinary
              (by simpa only [hbinaryVal] using hleftFit)
          rw [hstart] at hactualStart
          rw [hstop] at hactualStop
          cases hactualStart
          cases hactualStop
          have hwindow := hdomain.window start.val (subtreeCapacity factor binary.val)
          have heq := hwindow.length_eq_of_empty (Nat.min_le_right _ _) (by
            rintro ⟨index, hindex, query, value, hquery, hget⟩
            have hnone := ProgressiveTree.has_updates_in_range_false_excludes ValueInst mapInst
              (hrange.excludesValues.here hgeometry) hempty hget (by omega) (by omega)
            cases hnone)
          rw [hstartExact, hbinaryVal] at heq
          exact ⟨heq ▸ holdLeft, hleftFit⟩
        · obtain ⟨hfit, hdense⟩ := ProgressiveTree.updated_layer_dense ValueInst mapInst updates
            hlayout (hrange.here hgeometry (ProgressiveTree.has_updates_in_range_true ValueInst mapInst hhas).1)
            (hrange.binary hgeometry hhas) hdomain hnext hstart hbinary hhas holdLeft hupdate
          exact ⟨hdense, hfit⟩
      exact finishNode newHash newLeft newRight leftCorrect.1 leftCorrect.2 hnewRight hnewRightFit

/-- Recursive progressive bulk update preserves density and capacities from
the numeric extension bound at the supplied maximum. No semantic law bounding
all pending values by that maximum is required; range laws and the complete
dense update domain justify the traversed and skipped layers. -/
theorem ProgressiveTree.with_updated_leaves_recursive_dense_of_extent {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} {oldLength : Nat} {newLength : Std.Usize}
    (hextent : newLength.val ≤ maximum.elim oldLength (fun last => max (last.val + 1) oldLength))
    (hdomain : DenseUpdateDomain oldLength newLength.val (update_map.HasValueAt mapInst updates))
    {before after : ProgressiveTree T} {depth : Std.U32}
    (hrange : before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum depth)
    (hdense : before.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val))
    (hfit : before.Fits factor depth.val)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (core.result.Result.Ok after)) :
    after.Dense factor depth.val (newLength.val - progressiveCapacity factor depth.val) ∧
      after.Fits factor depth.val := by
  exact bulk_dense_aux ValueInst mapInst updates hlayout hextent hdomain
    (Std.U32.max - depth.val) depth before after (Nat.le_refl _) hdense hfit hrange hupdate

/-- Public progressive bulk update needs only the numeric extension bound
for its actual maximum answer, independently of the locations of pending values
within the old backing. Density still uses the complete update domain and the
range laws at reached queries. -/
theorem ProgressiveTree.with_updated_leaves_dense_of_extent {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {oldLength : Nat} {newLength : Std.Usize}
    (hextent : ∀ maximum, mapInst.max_index updates = ok maximum →
      newLength.val ≤ maximum.elim oldLength (fun last => max (last.val + 1) oldLength))
    (hdomain : DenseUpdateDomain oldLength newLength.val (update_map.HasValueAt mapInst updates))
    {before after : ProgressiveTree T}
    (hrange : ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
        ValueInst mapInst updates factor maximum 0#u32)
    (hdense : before.Dense factor 0 oldLength) (hfit : before.Fits factor 0)
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates =
      ok (core.result.Result.Ok after)) :
    after.Dense factor 0 newLength.val ∧ after.Fits factor 0 := by
  unfold ProgressiveTree.with_updated_leaves at hupdate
  cases hmax : mapInst.max_index updates with
  | fail e => simp [hmax] at hupdate
  | div => simp [hmax] at hupdate
  | ok maximum =>
    simp only [hmax, bind_tc_ok] at hupdate
    have hdense' : before.Dense factor (0#u32).val (oldLength - progressiveCapacity factor (0#u32).val) := by
      simpa [progressiveCapacity] using hdense
    have hresult := ProgressiveTree.with_updated_leaves_recursive_dense_of_extent ValueInst mapInst updates
      hlayout (hextent maximum hmax) hdomain (hrange maximum hmax) hdense' hfit hupdate
    simpa [progressiveCapacity] using hresult

/-- The previous semantic maximum contract supplies the numeric extension
bound as a sufficient special case. -/
theorem ProgressiveTree.with_updated_leaves_recursive_dense {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {maximum : Option Std.Usize} (hmaximum : update_map.MaximumBoundsValues mapInst updates maximum)
    {oldLength : Nat} {newLength : Std.Usize}
    (hdomain : DenseUpdateDomain oldLength newLength.val (update_map.HasValueAt mapInst updates))
    {before after : ProgressiveTree T} {depth : Std.U32}
    (hrange : before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
      ValueInst mapInst updates factor maximum depth)
    (hdense : before.Dense factor depth.val (oldLength - progressiveCapacity factor depth.val))
    (hfit : before.Fits factor depth.val)
    (hupdate : ProgressiveTree.with_updated_leaves_recursive ValueInst mapInst before updates maximum depth =
      ok (core.result.Result.Ok after)) :
    after.Dense factor depth.val (newLength.val - progressiveCapacity factor depth.val) ∧
      after.Fits factor depth.val := by
  exact ProgressiveTree.with_updated_leaves_recursive_dense_of_extent ValueInst mapInst updates hlayout
    ((update_map.extensionComplete_of_denseUpdateDomain mapInst updates hdomain).length_le_maximum_extent hmaximum)
    hdomain hrange hdense hfit hupdate

/-- Semantic maximum correctness implies the weaker numeric condition for
the actual public maximum query; existing callers retain this adapter. -/
theorem ProgressiveTree.with_updated_leaves_dense {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hmaximum : ∀ maximum, mapInst.max_index updates = ok maximum →
      update_map.MaximumBoundsValues mapInst updates maximum)
    {oldLength : Nat} {newLength : Std.Usize}
    (hdomain : DenseUpdateDomain oldLength newLength.val (update_map.HasValueAt mapInst updates))
    {before after : ProgressiveTree T}
    (hrange : ∀ maximum, mapInst.max_index updates = ok maximum →
      before.BulkRangeOn (update_map.RangeReflectsValuesAt mapInst updates)
        ValueInst mapInst updates factor maximum 0#u32)
    (hdense : before.Dense factor 0 oldLength) (hfit : before.Fits factor 0)
    (hupdate : ProgressiveTree.with_updated_leaves ValueInst mapInst before updates =
      ok (core.result.Result.Ok after)) :
    after.Dense factor 0 newLength.val ∧ after.Fits factor 0 := by
  exact ProgressiveTree.with_updated_leaves_dense_of_extent ValueInst mapInst updates hlayout
    (fun maximum hmax =>
      (update_map.extensionComplete_of_denseUpdateDomain mapInst updates hdomain).length_le_maximum_extent
        (hmaximum maximum hmax)) hdomain hrange hdense hfit hupdate

end milhouse.progressive_tree
