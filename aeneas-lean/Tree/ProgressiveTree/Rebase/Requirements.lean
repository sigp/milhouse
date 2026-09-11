import Tree.Rebase.GeometrySuccess
import Tree.ProgressiveTree.Rebase.Geometry
import Tree.ProgressiveTree.Rebase.Comparisons
import Tree.ProgressiveTree.Bounds

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- The actual layer-length calculation, retaining both machine-size clamps.
It remains valid beyond the capacity range used by indexed traversal proofs. -/
def rebaseLayerLength (factor : Option Std.Usize) (length depth : Nat) : Nat :=
  min (length - min Std.Usize.max (progressiveCapacity factor depth))
    (min Std.Usize.max (subtreeCapacity factor (2 * depth)))

/-- Successful metadata calls compute the clamped layer length without a
representability, shape, density, or input-length consistency assumption. -/
theorem ProgressiveTree.rebase_layer_length_clamped {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize}
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor)
    {depth next : Std.U32} {start capacity length localLength : Std.Usize}
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hnext : depth + 1#u32 = ok next)
    (hcapacity : ProgressiveTree.capacity_at_depth ValueInst next = ok capacity)
    (hmin : core.cmp.Ord.min.trait_default core.cmp.OrdUsize
      (core.num.Usize.saturating_sub length start) capacity = ok localLength) :
    localLength.val = rebaseLayerLength factor length.val depth.val := by
  obtain ⟨actualStart, hactualStart, hstartVal⟩ := ProgressiveTree.total_capacity_eq ValueInst hfactor depth
  rw [hstart] at hactualStart
  cases hactualStart
  obtain ⟨actualCapacity, hactualCapacity, hcapacityVal⟩ := ProgressiveTree.capacity_successor_eq ValueInst hfactor hnext
  rw [hcapacity] at hactualCapacity
  cases hactualCapacity
  obtain ⟨actualMin, hactualMin, hminVal⟩ := WP.spec_imp_exists
    (core.cmp.Ord.min.trait_default_Usize.spec (core.num.Usize.saturating_sub length start) capacity)
  rw [hmin] at hactualMin
  cases hactualMin
  rw [hminVal, core.cmp.impls.OrdUsize.min_val, usize_saturating_sub_val, hstartVal, hcapacityVal]
  rfl

/-- On representable layers, the general clamped input agrees with the older
mathematical comparison scope. -/
theorem rebaseLayerLength_of_fits {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth) (length depth : Nat)
    (hfit : subtreeCapacity factor (2 * depth) < 2 ^ System.Platform.numBits) :
    rebaseLayerLength factor length depth =
      min (length - progressiveCapacity factor depth) (subtreeCapacity factor (2 * depth)) := by
  have hstart := progressiveCapacity_lt_layer hlayout.leafCapacity_pos depth
  have hstartBound : progressiveCapacity factor depth ≤ Std.Usize.max := by scalar_tac
  have hcapacityBound : subtreeCapacity factor (2 * depth) ≤ Std.Usize.max := by scalar_tac
  unfold rebaseLayerLength
  rw [min_eq_right hstartBound, min_eq_right hcapacityBound]

/-- Input conditions for successful progressive rebasing. Only entered pairs
of nodes need checked depth arithmetic, the binary rebase's selected geometry
and element calls, and the remaining suffix conditions. All binary metadata
uses the actual clamped lengths. No rebase or metadata subcall success appears
in this predicate. -/
def ProgressiveTree.RebaseRequirements {T : Type} (inst : core.cmp.PartialEq T T) :
    ProgressiveTree T → ProgressiveTree T → Option Std.Usize → Nat → Nat → Nat → Nat → Prop
  | .ProgressiveNode hash left right, .ProgressiveNode baseHash baseLeft baseRight,
      factor, packingDepth, origLength, baseLength, depth =>
      triomphe.arc.Arc.ptr_eq (.ProgressiveNode hash left right : ProgressiveTree T)
        (.ProgressiveNode baseHash baseLeft baseRight) = ok false →
      depth + 1 ≤ Std.U32.max ∧ 2 * depth + packingDepth ≤ Std.Usize.max ∧
      left.RebaseGeometry baseLeft
        (some (rebaseLayerLength factor origLength depth, rebaseLayerLength factor baseLength depth))
        (2 * depth + packingDepth) ∧
      left.RebaseComparisons inst baseLeft
        (some (rebaseLayerLength factor origLength depth, rebaseLayerLength factor baseLength depth))
        (2 * depth + packingDepth) ∧
      right.RebaseRequirements inst baseRight factor packingDepth origLength baseLength (depth + 1)
  | _, _, _, _, _, _, _ => True

/-- A missing or shared progressive input omits every arithmetic, shape, and
element-call condition in that suffix. -/
theorem ProgressiveTree.rebaseRequirements_of_stop {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : ProgressiveTree T) (factor : Option Std.Usize)
    (packingDepth origLength baseLength depth : Nat)
    (hstop : orig = .ProgressiveZero ∨ base = .ProgressiveZero ∨
      triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseRequirements inst base factor packingDepth origLength baseLength depth := by
  rcases hstop with rfl | rfl | hpointer
  · cases base <;> trivial
  · cases orig <;> trivial
  · cases orig <;> cases base <;> simp only [ProgressiveTree.RebaseRequirements]
    intro hfalse
    rw [hpointer] at hfalse
    cases hfalse

/-- Whole-tree shape and capacity invariants supply the weaker selected
requirements from the previous comparison scope. This is an adapter, not an
extra assumption on the general success characterization. -/
theorem ProgressiveTree.rebaseRequirements_of_invariants {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : ProgressiveTree T} {origLength baseLength depth : Nat}
    (horig : orig.Shape factor depth) (hbase : base.Shape factor depth)
    (hfit : orig.Fits factor depth)
    (hcompare : orig.RebaseComparisons ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength baseLength depth) :
    orig.RebaseRequirements ValueInst.corecmpPartialEqInst base factor
      packingDepth.val origLength baseLength depth := by
  induction orig generalizing base depth with
  | ProgressiveZero => cases base <;> trivial
  | ProgressiveNode hash left right ih =>
    cases base with
    | ProgressiveZero => trivial
    | ProgressiveNode baseHash baseLeft baseRight =>
      cases horig with
      | node _ hleft hright =>
        cases hbase with
        | node _ hbaseLeft hbaseRight =>
          intro hpointer
          have hbits : packingDepth.val + 2 * depth < System.Platform.numBits := by
            have hcapacity := hfit.1
            rw [hlayout.subtreeCapacity_eq_two_pow] at hcapacity
            by_contra hnot
            have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
              (show System.Platform.numBits ≤ packingDepth.val + 2 * depth by omega)
            omega
          have hplatform : System.Platform.numBits ≤ 64 := by cases System.Platform.numBits_eq <;> omega
          have hword : 64 ≤ Std.Usize.max := by scalar_tac
          refine ⟨?_, by omega, ?_, ?_, ih hright hbaseRight hfit.2 (hcompare hpointer).2⟩
          · norm_num [U32.max, U32.numBits]
            omega
          · exact Tree.rebaseGeometry_of_shape hleft hbaseLeft (by omega)
              (fun _ => by rw [UScalarTy.Usize_numBits_eq]; omega)
          · simpa only [rebaseLayerLength_of_fits hlayout origLength depth hfit.1,
              rebaseLayerLength_of_fits hlayout baseLength depth hfit.1] using (hcompare hpointer).1

end milhouse.progressive_tree
