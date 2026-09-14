import Tree.Shape

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Materialized values in left-to-right leaf order. Zero padding contributes
    no values. Density is needed to identify this sequence with tree indices:
    a sparse tree can have holes before its materialized values. -/
def Tree.elements {T : Type} : Tree T → _root_.List T
  | .Zero _ => []
  | .Leaf value => [value.value]
  | .PackedLeaf value => value.values.val
  | .Node _ left right => left.elements ++ right.elements

/-- A dense tree's recorded logical length counts its materialized values. -/
theorem DenseTree.elements_length {T : Type} {factor : Option Std.Usize}
    {self : Tree T} {depth length : Nat} (hdense : DenseTree factor self depth length) :
    self.elements.length = length := by
  induction hdense <;> simp_all [Tree.elements]

/-- Dense tree slots are exactly the stored sequence, with the same wrapping
    modulo capacity as Rust's binary-tree lookup. This pure contents theorem
    requires no packing-operation laws or machine arithmetic bounds. -/
theorem DenseTree.slot_eq_elements_mod {T : Type} {factor : Option Std.Usize}
    {self : Tree T} {depth length : Nat} (hdense : DenseTree factor self depth length)
    (index : Nat) :
    self.slot factor depth index = self.elements[index % subtreeCapacity factor depth]? := by
  induction hdense with
  | zero factor depth => simp [Tree.slot, Tree.elements]
  | leaf value => simp [Tree.slot, Tree.elements, subtreeCapacity, leafCapacity, Nat.mod_one]
  | packed factor value hnonempty hfit =>
    simp [Tree.slot, Tree.elements, subtreeCapacity, leafCapacity]
  | node factor hash left right child leftLen rightLen hleft hright hnonempty hfull ihleft ihright =>
    have hleftLen := hleft.elements_length
    have hrightLen := hright.elements_length
    have hleftBound := hleft.length_le_capacity
    have hpositive : 0 < subtreeCapacity factor child := by omega
    have hcapacity : subtreeCapacity factor (child + 1) = subtreeCapacity factor child * 2 := by
      simp [subtreeCapacity, pow_succ, Nat.mul_assoc]
    simp only [Tree.slot, Tree.elements, ihleft, ihright]
    by_cases hroute : index % subtreeCapacity factor (child + 1) < subtreeCapacity factor child
    · rw [if_pos hroute]
      have hmod : index % subtreeCapacity factor child =
          index % subtreeCapacity factor (child + 1) := by
        rw [hcapacity] at hroute ⊢
        exact mod_child_eq_parent_of_lt index (subtreeCapacity factor child) hroute
      rw [hmod]
      by_cases hinside : index % subtreeCapacity factor (child + 1) < left.elements.length
      · exact (_root_.List.getElem?_append_left hinside).symm
      · have hrightZero : rightLen = 0 := by
          by_contra hne
          have hleftFull := hfull (by omega)
          omega
        have hrightNil : right.elements = [] :=
          _root_.List.eq_nil_of_length_eq_zero (hrightLen.trans hrightZero)
        simp [hrightNil]
    · rw [if_neg hroute]
      have hmod : index % subtreeCapacity factor child =
          index % subtreeCapacity factor (child + 1) - subtreeCapacity factor child := by
        rw [hcapacity] at hroute ⊢
        exact mod_child_eq_parent_sub_of_not_lt index (subtreeCapacity factor child) hpositive hroute
      rw [hmod]
      by_cases hrightPositive : 0 < rightLen
      · have hleftFull := hfull hrightPositive
        rw [_root_.List.getElem?_append_right (by omega), hleftLen, hleftFull]
      · have hrightZero : rightLen = 0 := by omega
        have hrightNil : right.elements = [] :=
          _root_.List.eq_nil_of_length_eq_zero (hrightLen.trans hrightZero)
        simp only [hrightNil, _root_.List.getElem?_nil, _root_.List.append_nil]
        symm
        exact _root_.List.getElem?_eq_none_iff.mpr (by omega)

/-- Extracted binary-tree lookup returns the corresponding materialized
    element, including missing positions after the dense prefix. The modulo
    records the operation's behavior outside its subtree capacity. -/
theorem DenseTree.get_recursive_eq_elements_mod {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {self : Tree T} {depth packingDepth : Std.Usize}
    {length : Nat} (hdense : DenseTree factor self depth.val length)
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hbits : depth.val + packingDepth.val ≤ System.Platform.numBits) (index : Std.Usize) :
    Tree.get_recursive ValueInst self index depth packingDepth =
      ok self.elements[index.val % subtreeCapacity factor depth.val]? := by
  rw [hdense.shape.get_recursive_eq_slot hlayout depth rfl hbits,
    hdense.slot_eq_elements_mod]

/-- Within its capacity, a dense binary tree implements ordinary sequence
    indexing, including the unmaterialized suffix. -/
theorem DenseTree.get_recursive_eq_elements {T : Type} {ValueInst : Value T}
    {factor : Option Std.Usize} {self : Tree T} {depth packingDepth : Std.Usize}
    {length : Nat} (hdense : DenseTree factor self depth.val length)
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (hbits : depth.val + packingDepth.val ≤ System.Platform.numBits) (index : Std.Usize)
    (hindex : index.val < subtreeCapacity factor depth.val) :
    Tree.get_recursive ValueInst self index depth packingDepth = ok self.elements[index.val]? := by
  rw [hdense.get_recursive_eq_elements_mod hlayout hbits, Nat.mod_eq_of_lt hindex]

end milhouse.tree
