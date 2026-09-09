import Tree.ProgressiveTree.Bounds

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Every progressive layer needed by the given sequence length has a
representable binary capacity. An unused next layer imposes no bound. -/
def ProgressiveTree.LengthFits (factor : Option Std.Usize) (length : Nat) : Prop :=
  ∀ depth, progressiveCapacity factor depth < length →
    subtreeCapacity factor (2 * depth) ≤ Std.Usize.max

theorem ProgressiveTree.LengthFits.zero (factor : Option Std.Usize) :
    ProgressiveTree.LengthFits factor 0 := by
  intro depth h
  omega

/-- Any shorter sequence needs only layers already needed by the longer one. -/
theorem ProgressiveTree.LengthFits.mono {factor : Option Std.Usize} {length smaller : Nat}
    (hfits : ProgressiveTree.LengthFits factor length) (hle : smaller ≤ length) :
    ProgressiveTree.LengthFits factor smaller := by
  intro depth hdepth
  exact hfits depth (lt_of_lt_of_le hdepth hle)

private theorem ProgressiveTree.Dense.layer_bound {T : Type} {factor : Option Std.Usize}
    {self : ProgressiveTree T} {start length : Nat}
    (hdense : self.Dense factor start length) (hfits : self.Fits factor start) :
    ∀ depth, start ≤ depth → progressiveCapacity factor depth <
      progressiveCapacity factor start + length →
      subtreeCapacity factor (2 * depth) < 2 ^ System.Platform.numBits := by
  induction hdense with
  | zero start =>
    intro depth hle hinside
    have hmono := progressiveCapacity_mono factor hle
    omega
  | @node start leftLength rightLength left right hash hleft hright hfull ih =>
    intro depth hle hinside
    by_cases heq : depth = start
    · simpa only [heq] using hfits.1
    · apply ih hfits.2 depth (by omega)
      have hbound := hleft.length_le_capacity
      rw [progressiveCapacity_succ]
      omega

/-- A dense tree with representable layers supplies the sequence-capacity
bound needed to reconstruct its contents. No packing law is required. -/
theorem ProgressiveTree.Dense.lengthFits {T : Type} {factor : Option Std.Usize}
    {self : ProgressiveTree T} {length : Nat}
    (hdense : self.Dense factor 0 length) (hfits : self.Fits factor 0) :
    ProgressiveTree.LengthFits factor length := by
  intro depth hinside
  have hbound := hdense.layer_bound hfits depth (Nat.zero_le _)
    (by simpa only [progressiveCapacity_zero, Nat.zero_add] using hinside)
  have hmax : Std.Usize.max + 1 = 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp_all [Std.Usize.max, Std.Usize.numBits]
  omega

end milhouse.progressive_tree
