import Tree.Iter.Path
import Tree.TrailingZeros

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.iter

/-- Within a packed leaf, incrementing the index without crossing a chunk
    boundary preserves the entire saved path. -/
theorem Path.advance_in_chunk {T : Type} {packingDepth depth index : Nat}
    {root : tree.Tree T} {stack : _root_.List (tree.Tree T)}
    (h : Path packingDepth root depth index stack)
    (hfull : stack.length = depth + 1)
    (hboundary : ¬ 2 ^ packingDepth ∣ index + 1) :
    Path packingDepth root depth (index + 1) stack := by
  apply h.congr_index
  simpa [hfull] using (Nat.succ_div_of_not_dvd hboundary).symm

/-- Rust's trailing-zero backtracking count leaves exactly a reusable search
    prefix for the next index. This includes popping every frame at the end of
    a tree. The packing divisibility premise is the chunk-boundary condition. -/
theorem Path.backtrack {T : Type} {packingDepth depth index : Nat}
    {root : tree.Tree T} {stack : _root_.List (tree.Tree T)}
    (h : Path packingDepth root depth index stack)
    (hfull : stack.length = depth + 1)
    (hboundary : 2 ^ packingDepth ∣ index + 1) :
    Path packingDepth root depth (index + 1)
      (stack.take (stack.length - (padicValNat 2 (index + 1) - packingDepth + 1))) := by
  have hpacking : packingDepth ≤ padicValNat 2 (index + 1) :=
    (padicValNat_dvd_iff_le (p := 2) (by omega)).mp hboundary
  by_cases hkeep : padicValNat 2 (index + 1) - packingDepth + 1 < stack.length
  · apply h.take_congr_index
    have hexponent : depth + 1 -
        min (stack.length - (padicValNat 2 (index + 1) - packingDepth + 1)) stack.length +
        packingDepth = padicValNat 2 (index + 1) + 1 := by omega
    rw [hexponent]
    exact (Nat.succ_div_of_not_dvd (pow_succ_padicValNat_not_dvd (p := 2) (by omega))).symm
  · have hzero : stack.length - (padicValNat 2 (index + 1) - packingDepth + 1) = 0 := by omega
    rw [hzero, _root_.List.take_zero]
    exact .nil _ _ _

/-- Before the end of the root capacity, the same backtracking count retains
    at least one ancestor. A live iterator therefore cannot lose its stack. -/
theorem backtrack_nonempty {T : Type} {packingDepth depth index : Nat}
    {stack : _root_.List (tree.Tree T)}
    (hfull : stack.length = depth + 1)
    (hboundary : 2 ^ packingDepth ∣ index + 1)
    (hinside : index + 1 < 2 ^ (depth + packingDepth)) :
    stack.take (stack.length - (padicValNat 2 (index + 1) - packingDepth + 1)) ≠ [] := by
  have hpacking : packingDepth ≤ padicValNat 2 (index + 1) :=
    (padicValNat_dvd_iff_le (p := 2) (by omega)).mp hboundary
  have hval : padicValNat 2 (index + 1) < depth + packingDepth := by
    by_contra hnot
    have hpow := Nat.pow_le_pow_right (n := 2) (by omega) (by omega : depth + packingDepth ≤ padicValNat 2 (index + 1))
    have hle : 2 ^ padicValNat 2 (index + 1) ≤ index + 1 :=
      Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    omega
  intro hempty
  have hlength := congrArg _root_.List.length hempty
  simp only [_root_.List.length_take, _root_.List.length_nil] at hlength
  omega

end milhouse.iter
