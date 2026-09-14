import Tree.Contents
import Tree.ProgressiveTree.Shape

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Materialized values in increasing spine order, with each binary subtree
    contributing its values in leaf order. -/
def ProgressiveTree.elements {T : Type} : ProgressiveTree T → _root_.List T
  | .ProgressiveZero => []
  | .ProgressiveNode _ left right => left.elements ++ right.elements


/-- Each binary layer stores a dense prefix, and every layer preceding a
    nonempty suffix is full. Empty internal nodes are allowed: their presence
    does not affect the represented sequence. -/
inductive ProgressiveTree.Dense {T : Type} :
    Option Std.Usize → ProgressiveTree T → Nat → Nat → Prop where
  | zero (factor : Option Std.Usize) (depth : Nat) :
      Dense factor .ProgressiveZero depth 0
  | node {factor : Option Std.Usize} {depth leftLength rightLength : Nat}
      {left : tree.Tree T} {right : ProgressiveTree T}
      (hash : lock_api.rwlock.RwLock parking_lot.raw_rwlock.RawRwLock
        (alloy_primitives.bits.fixed.FixedBytes 32#usize))
      (hleft : DenseTree factor left (2 * depth) leftLength)
      (hright : Dense factor right (depth + 1) rightLength)
      (hfull : 0 < rightLength → leftLength = subtreeCapacity factor (2 * depth)) :
      Dense factor (.ProgressiveNode hash left right) depth (leftLength + rightLength)

theorem ProgressiveTree.Dense.elements_length {T : Type} {factor : Option Std.Usize}
    {self : ProgressiveTree T} {depth length : Nat}
    (hdense : self.Dense factor depth length) : self.elements.length = length := by
  induction hdense with
  | zero => rfl
  | node hash hleft hright hfull ih =>
    simp [ProgressiveTree.elements, hleft.elements_length, ih]

theorem ProgressiveTree.Dense.shape {T : Type} {factor : Option Std.Usize}
    {self : ProgressiveTree T} {depth length : Nat}
    (hdense : self.Dense factor depth length) : self.Shape factor depth := by
  induction hdense with
  | zero => exact .zero _ _
  | node hash hleft hright hfull ih => exact .node hash hleft.shape ih

/-- Density supplies the existing spine-ending invariant at the end of its
    sequence, accounting for the starting offset of a non-root suffix. -/
theorem ProgressiveTree.Dense.endsAfter {T : Type} {factor : Option Std.Usize}
    {self : ProgressiveTree T} {depth length : Nat}
    (hdense : self.Dense factor depth length) :
    self.EndsAfter factor depth (progressiveCapacity factor depth + length) := by
  induction hdense with
  | zero => simp [ProgressiveTree.EndsAfter]
  | @node depth leftLength rightLength left right hash hleft hright hfull ih =>
    apply ih.mono
    have hbound := hleft.length_le_capacity
    rw [progressiveCapacity_succ]
    omega

/-- A mathematical lookup indexed relative to the start of this spine suffix.
    Binary layers are selected by their capacities; zero padding contributes
    missing slots rather than shifting subsequent values. -/
def ProgressiveTree.slot {T : Type} (factor : Option Std.Usize) :
    ProgressiveTree T → Nat → Nat → Option T
  | .ProgressiveZero, _, _ => none
  | .ProgressiveNode _ left right, depth, index =>
    if index < subtreeCapacity factor (2 * depth)
    then left.slot factor (2 * depth) index
    else right.slot factor (depth + 1) (index - subtreeCapacity factor (2 * depth))

/-- Dense progressive slots are precisely sequence indexing, including the
    missing suffix. This theorem has no machine bounds or packing-law premise. -/
theorem ProgressiveTree.Dense.slot_eq_elements {T : Type} {factor : Option Std.Usize}
    {self : ProgressiveTree T} {depth length : Nat}
    (hdense : self.Dense factor depth length) (index : Nat) :
    self.slot factor depth index = self.elements[index]? := by
  induction hdense generalizing index with
  | zero => simp [ProgressiveTree.slot, ProgressiveTree.elements]
  | @node depth leftLength rightLength left right hash hleft hright hfull ih =>
    have hleftLen := hleft.elements_length
    have hrightLen := hright.elements_length
    have hleftBound := hleft.length_le_capacity
    simp only [ProgressiveTree.slot, ProgressiveTree.elements]
    by_cases hroute : index < subtreeCapacity factor (2 * depth)
    · rw [if_pos hroute, hleft.slot_eq_elements_mod, Nat.mod_eq_of_lt hroute]
      by_cases hinside : index < left.elements.length
      · exact (_root_.List.getElem?_append_left hinside).symm
      · have hrightZero : rightLength = 0 := by
          by_contra hne
          have hleftFull := hfull (by omega)
          omega
        have hrightNil : right.elements = [] :=
          _root_.List.eq_nil_of_length_eq_zero (hrightLen.trans hrightZero)
        simp [hrightNil]
    · rw [if_neg hroute, ih]
      by_cases hrightPositive : 0 < rightLength
      · have hleftFull := hfull hrightPositive
        rw [_root_.List.getElem?_append_right (by omega), hleftLen, hleftFull]
      · have hrightZero : rightLength = 0 := by omega
        have hrightNil : right.elements = [] :=
          _root_.List.eq_nil_of_length_eq_zero (hrightLen.trans hrightZero)
        simp only [hrightNil, _root_.List.getElem?_nil, _root_.List.append_nil]
        symm
        exact _root_.List.getElem?_eq_none_iff.mpr (by omega)

end milhouse.progressive_tree
