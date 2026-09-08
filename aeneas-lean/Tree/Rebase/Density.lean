import Tree.Rebase
import Tree.Contents

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

theorem DenseTree.split_node {T : Type} {factor : Option Std.Usize}
    {hash : alloy_primitives.bits.fixed.FixedBytes 32#usize}
    {left right : Tree T} {depth length : Nat}
    (hdense : DenseTree factor (.Node hash left right) (depth + 1) length) :
    DenseTree factor left depth (min length (subtreeCapacity factor depth)) ∧
      DenseTree factor right depth (length - subtreeCapacity factor depth) := by
  cases hdense with
  | node _ _ _ _ depth leftLength rightLength hleft hright hpositive hfull =>
    have hbound := hleft.length_le_capacity
    have hleftLen : min (leftLength + rightLength) (subtreeCapacity factor depth) = leftLength := by
      by_cases hr : 0 < rightLength
      · have := hfull hr
        omega
      · omega
    have hrightLen : leftLength + rightLength - subtreeCapacity factor depth = rightLength := by
      by_cases hr : 0 < rightLength
      · have := hfull hr
        omega
      · omega
    rw [hleftLen, hrightLen]
    exact ⟨hleft, hright⟩

/-- A positional mixture of two dense prefixes has a length between theirs,
    even when the inputs have different lengths. This does not yet claim that
    an arbitrary mixture is itself dense. -/
theorem PositionalMix.length_bounds {T : Type} {factor : Option Std.Usize}
    {orig base mixed : Tree T} {depth origLength baseLength : Nat}
    (hmix : PositionalMix orig base mixed)
    (horig : DenseTree factor orig depth origLength)
    (hbase : DenseTree factor base depth baseLength) :
    min origLength baseLength ≤ mixed.elements.length ∧
      mixed.elements.length ≤ max origLength baseLength := by
  induction hmix generalizing depth origLength baseLength with
  | orig orig base => simp only [horig.elements_length]; omega
  | base orig base => simp only [hbase.elements_length]; omega
  | node origHash baseHash newHash origLeft origRight baseLeft baseRight newLeft newRight
      leftMix rightMix ihLeft ihRight =>
    obtain ⟨child, hdepth⟩ : ∃ child, depth = child + 1 := by
      cases horig with
      | node _ _ _ _ child _ _ _ _ _ _ => exact ⟨child, rfl⟩
    subst depth
    obtain ⟨origLeftDense, origRightDense⟩ := horig.split_node
    obtain ⟨baseLeftDense, baseRightDense⟩ := hbase.split_node
    have hleft := ihLeft origLeftDense baseLeftDense
    have hright := ihRight origRightDense baseRightDense
    simp only [Tree.elements, List.length_append]
    constructor <;> omega

/-- If a positional mixture retains the original length, it retains the
    original dense prefix. The base may have any dense length at this depth;
    length preservation rules out introducing holes or extra materialization. -/
theorem PositionalMix.preserves_dense_of_length {T : Type} {factor : Option Std.Usize}
    {orig base mixed : Tree T} {depth origLength baseLength : Nat}
    (hmix : PositionalMix orig base mixed)
    (horig : DenseTree factor orig depth origLength)
    (hbase : DenseTree factor base depth baseLength)
    (hlength : mixed.elements.length = origLength) :
    DenseTree factor mixed depth origLength := by
  induction hmix generalizing depth origLength baseLength with
  | orig orig base => exact horig
  | base orig base =>
    have heq := hbase.elements_length.symm.trans hlength
    exact heq ▸ hbase
  | node origHash baseHash newHash origLeft origRight baseLeft baseRight newLeft newRight
      leftMix rightMix ihLeft ihRight =>
    obtain ⟨child, hdepth⟩ : ∃ child, depth = child + 1 := by
      cases horig with
      | node _ _ _ _ child _ _ _ _ _ _ => exact ⟨child, rfl⟩
    subst depth
    obtain ⟨origLeftDense, origRightDense⟩ := horig.split_node
    obtain ⟨baseLeftDense, baseRightDense⟩ := hbase.split_node
    have hleftBounds := leftMix.length_bounds origLeftDense baseLeftDense
    have hrightBounds := rightMix.length_bounds origRightDense baseRightDense
    simp only [Tree.elements, List.length_append] at hlength
    have hleftLen : newLeft.elements.length = min origLength (subtreeCapacity factor child) := by omega
    have hrightLen : newRight.elements.length = origLength - subtreeCapacity factor child := by omega
    have hleft := ihLeft origLeftDense baseLeftDense hleftLen
    have hright := ihRight origRightDense baseRightDense hrightLen
    have hpositive : 0 < min origLength (subtreeCapacity factor child) := by
      cases horig with
      | node _ _ _ _ _ _ _ hsourceLeft _ hpos hfull =>
        have := hsourceLeft.length_le_capacity
        omega
    have hsum : origLength = min origLength (subtreeCapacity factor child) +
        (origLength - subtreeCapacity factor child) := by omega
    rw [hsum]
    exact .node factor newHash newLeft newRight child _ _ hleft hright hpositive (by omega)

end milhouse.tree
