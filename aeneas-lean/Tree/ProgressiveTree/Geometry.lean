import Tree.ProgressiveTree.Capacity
import Tree.ProgressiveTree.Depth

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_tree

/-- Mathematical start of a progressive layer, before machine-size clamping. -/
def progressiveCapacity (factor : Option Std.Usize) (depth : Nat) : Nat :=
  ((4 ^ depth - 1) / 3) * tree.leafCapacity factor

@[simp] theorem progressiveCapacity_zero (factor : Option Std.Usize) :
    progressiveCapacity factor 0 = 0 := by
  simp [progressiveCapacity]

/-- A progressive layer contains the binary subtree with twice its depth. -/
theorem progressiveCapacity_succ (factor : Option Std.Usize) (depth : Nat) :
    progressiveCapacity factor (depth + 1) = progressiveCapacity factor depth +
      tree.subtreeCapacity factor (2 * depth) := by
  have hpower : 2 ^ (2 * depth) = 4 ^ depth := by rw [pow_mul]; rfl
  simp only [progressiveCapacity, progressive_sum_succ, Nat.add_mul,
    tree.subtreeCapacity, hpower, Nat.mul_comm (4 ^ depth)]

/-- Three copies of the completed prefix, plus one packed leaf, fill the next
layer. This exact geometric identity also bounds counters near machine limits. -/
theorem progressiveCapacity_layer_relation (factor : Option Std.Usize) (depth : Nat) :
    3 * progressiveCapacity factor depth + tree.leafCapacity factor =
      tree.subtreeCapacity factor (2 * depth) := by
  induction depth with
  | zero => simp [tree.subtreeCapacity]
  | succ depth ih =>
    have hstep : tree.subtreeCapacity factor (2 * (depth + 1)) =
        4 * tree.subtreeCapacity factor (2 * depth) := by
      simp only [tree.subtreeCapacity, Nat.mul_add, pow_add]
      ring
    rw [progressiveCapacity_succ, hstep]
    omega

theorem progressiveCapacity_mono (factor : Option Std.Usize) :
    Monotone (progressiveCapacity factor) := by
  intro left right hle
  apply Nat.mul_le_mul_right
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by decide) hle

theorem progressiveCapacity_aligned (factor : Option Std.Usize) (depth : Nat) :
    progressiveCapacity factor depth % tree.leafCapacity factor = 0 := by
  simp [progressiveCapacity]

/-- All preceding layers together occupy less space than the current layer. -/
theorem progressiveCapacity_lt_layer {factor : Option Std.Usize}
    (hpositive : 0 < tree.leafCapacity factor) (depth : Nat) :
    progressiveCapacity factor depth < tree.subtreeCapacity factor (2 * depth) := by
  have hpower : 2 ^ (2 * depth) = 4 ^ depth := by rw [pow_mul]; rfl
  have hpowPositive : 0 < 4 ^ depth := by positivity
  have hsum : (4 ^ depth - 1) / 3 < 4 ^ depth := by omega
  simpa only [progressiveCapacity, tree.subtreeCapacity, hpower,
    Nat.mul_comm (tree.leafCapacity factor)] using Nat.mul_lt_mul_of_pos_right hsum hpositive

/-- Extracted capacity always succeeds under the packing-factor query law. -/
theorem ProgressiveTree.total_capacity_eq {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize}
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor)
    (depth : Std.U32) :
    ∃ capacity, ProgressiveTree.total_capacity_at_depth ValueInst depth = ok capacity ∧
      capacity.val = min Std.Usize.max (progressiveCapacity factor depth.val) := by
  obtain ⟨capacity, hcapacity, hval⟩ :=
    ProgressiveTree.total_capacity_formula ValueInst depth hfactor
  refine ⟨capacity, hcapacity, ?_⟩
  cases factor <;> simpa [progressiveCapacity, tree.leafCapacity,
    core.option.Option.unwrap_or] using hval

theorem ProgressiveTree.total_capacity_zero {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize}
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor) :
    ProgressiveTree.total_capacity_at_depth ValueInst 0#u32 = ok 0#usize := by
  obtain ⟨capacity, hcapacity, hval⟩ := ProgressiveTree.total_capacity_eq ValueInst hfactor 0#u32
  have heq : capacity = 0#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hval
  simpa only [heq] using hcapacity

/-- A capacity strictly below the machine maximum is the mathematical layer
    start. In particular, the start of every nonempty machine-index window is
    unclamped, even before proving that its endpoint is unclamped. -/
theorem ProgressiveTree.total_capacity_unclamped {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize}
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor)
    {depth : Std.U32} {capacity : Std.Usize}
    (hcapacity : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok capacity)
    (hsmall : capacity.val < Std.Usize.max) :
    capacity.val = progressiveCapacity factor depth.val := by
  obtain ⟨actual, hactual, hval⟩ := ProgressiveTree.total_capacity_eq ValueInst hfactor depth
  rw [hcapacity] at hactual
  cases hactual
  omega

/-- Before saturation, advancing one layer gives a nonempty machine-index
    window. This also holds when the new endpoint itself saturates. -/
theorem ProgressiveTree.layer_nonempty {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {depth next : Std.U32} {start stop : Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hstart : ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start)
    (hstop : ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop)
    (hsmall : start.val < Std.Usize.max) :
    start.val < stop.val := by
  have hstartVal := ProgressiveTree.total_capacity_unclamped ValueInst
    hlayout.opt_packing_factor_eq hstart hsmall
  obtain ⟨actualStop, hactualStop, hstopVal⟩ :=
    ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq next
  rw [hstop] at hactualStop
  cases hactualStop
  have hadd := UScalar.add_equiv depth 1#u32
  rw [hnext] at hadd
  simp at hadd
  have hnextVal : next.val = depth.val + 1 := by omega
  have hpositive := hlayout.subtreeCapacity_pos (2 * depth.val)
  rw [hnextVal, progressiveCapacity_succ] at hstopVal
  omega

/-- A representable power-of-two layer also has representable endpoints.
    Thus the saturating capacity calculation does not truncate this window. -/
theorem progressiveCapacity_succ_fits {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth) (depth : Nat)
    (hfit : tree.subtreeCapacity factor (2 * depth) < 2 ^ System.Platform.numBits) :
    progressiveCapacity factor (depth + 1) < 2 ^ System.Platform.numBits := by
  have hsmall := progressiveCapacity_lt_layer hlayout.leafCapacity_pos depth
  have hexponent : packingDepth.val + 2 * depth < System.Platform.numBits := by
    rw [hlayout.subtreeCapacity_eq_two_pow] at hfit
    by_contra hnot
    have hle : System.Platform.numBits ≤ packingDepth.val + 2 * depth := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    omega
  have hdouble : 2 * tree.subtreeCapacity factor (2 * depth) ≤
      2 ^ System.Platform.numBits := by
    rw [hlayout.subtreeCapacity_eq_two_pow]
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show packingDepth.val + 2 * depth + 1 ≤ System.Platform.numBits by omega)
    simpa only [pow_succ, Nat.mul_comm] using hpow
  rw [progressiveCapacity_succ]
  omega

/-- The actual adjacent machine capacities delimit exactly one aligned binary
    subtree whenever that subtree's capacity is representable. The depth and
    packing laws supply the window arithmetic rather than assuming it. -/
theorem ProgressiveTree.layer_window {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {depth next : Std.U32} {binary : Std.Usize}
    (hnext : depth + 1#u32 = ok next)
    (hbinary : ProgressiveTree.prog_depth_to_binary_depth ValueInst next = ok binary)
    (hfit : tree.subtreeCapacity factor binary.val < 2 ^ System.Platform.numBits) :
    ∃ start stop,
      ProgressiveTree.total_capacity_at_depth ValueInst depth = ok start ∧
      ProgressiveTree.total_capacity_at_depth ValueInst next = ok stop ∧
      start.val = progressiveCapacity factor depth.val ∧
      stop.val = start.val + tree.subtreeCapacity factor binary.val ∧
      start.val % tree.leafCapacity factor = 0 := by
  have hbinaryVal := ProgressiveTree.binary_depth_successor_val ValueInst hnext hbinary
  have hadd := UScalar.add_equiv depth 1#u32
  rw [hnext] at hadd
  simp at hadd
  have hnextVal : next.val = depth.val + 1 := by omega
  rw [hbinaryVal] at hfit
  have hstopFit := progressiveCapacity_succ_fits hlayout depth.val hfit
  have hstartFit := lt_trans (progressiveCapacity_lt_layer hlayout.leafCapacity_pos depth.val) hfit
  obtain ⟨start, hstart, hstartVal⟩ :=
    ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq depth
  obtain ⟨stop, hstop, hstopVal⟩ :=
    ProgressiveTree.total_capacity_eq ValueInst hlayout.opt_packing_factor_eq next
  rw [min_eq_right (by scalar_tac)] at hstartVal
  rw [hnextVal, min_eq_right (by scalar_tac)] at hstopVal
  refine ⟨start, stop, hstart, hstop, hstartVal, ?_, ?_⟩
  · rw [hstopVal, hstartVal, hbinaryVal, progressiveCapacity_succ]
  · rw [hstartVal]
    exact progressiveCapacity_aligned factor depth.val

/-- Cached capacity equals the next binary layer's capacity, with only the
    final machine clamp remaining. This needs the packing query, not a full
    power-of-two layout law. -/
theorem ProgressiveTree.capacity_successor_eq {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {depth next : Std.U32}
    (hfactor : utils.opt_packing_factor ValueInst.tree_hashTreeHashInst = ok factor)
    (hnext : depth + 1#u32 = ok next) :
    ∃ capacity, ProgressiveTree.capacity_at_depth ValueInst next = ok capacity ∧
      capacity.val = min Std.Usize.max (tree.subtreeCapacity factor (2 * depth.val)) := by
  obtain ⟨capacity, hcapacity, hval⟩ := ProgressiveTree.capacity_successor_formula ValueInst hnext hfactor
  refine ⟨capacity, hcapacity, ?_⟩
  have hpower : 2 ^ (2 * depth.val) = 4 ^ depth.val := by rw [pow_mul]; rfl
  cases factor <;> simpa [tree.subtreeCapacity, tree.leafCapacity,
    core.option.Option.unwrap_or, hpower, Nat.mul_comm] using hval

end milhouse.progressive_tree
