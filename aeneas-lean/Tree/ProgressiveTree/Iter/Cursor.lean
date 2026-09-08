import Tree.ProgressiveTree.Iter.Enter

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Number of materialized binary layers still stored in a progressive spine. -/
def ProgressiveTree.layerCount {T : Type} : ProgressiveTree T → Nat
  | .ProgressiveZero => 0
  | .ProgressiveNode _ _ right => right.layerCount + 1

/-- Clearing the terminal zero is also a pending traversal step. -/
def ProgressiveTreeIter.pendingSteps {T : Type} : Option (ProgressiveTree T) → Nat
  | none => 0
  | some root => root.layerCount + 1

/-- The unopened spine suffix has its exact remaining global length and every
    materialized layer fits the machine's binary routing arithmetic. -/
def ProgressiveTreeIter.Pending {T : Type} (factor : Option Std.Usize)
    (length : Std.Usize) (depth : Std.U32) (node : Option (ProgressiveTree T))
    (values : _root_.List T) : Prop :=
  match node with
  | none => values = []
  | some root =>
    root.Dense factor depth.val (length.val - progressiveCapacity factor depth.val) ∧
      root.Fits factor depth.val ∧ values = root.elements

/-- The active binary iterator has already been proved to enumerate its suffix;
    an absent binary iterator contributes no values. -/
def ProgressiveTreeIter.Current {T : Type} (ValueInst : Value T)
    (current : Option (iter.Iter T)) (values : _root_.List T) : Prop :=
  match current with
  | none => values = []
  | some current =>
    IteratorDrains (iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next ValueInst)
      current values

/-- A progressive cursor represents the active binary suffix followed by the
    unopened spine. The value count bounds its checked yielded-counter updates.
    The binary iterator relation is supplied by the proved layer-entry theorem. -/
def ProgressiveTreeIter.Valid {T : Type} (ValueInst : Value T) (factor : Option Std.Usize)
    (self : ProgressiveTreeIter T) (values : _root_.List T) : Prop :=
  ∃ currentValues pendingValues,
    ProgressiveTreeIter.Current ValueInst self.current_iter currentValues ∧
    ProgressiveTreeIter.Pending factor self.length self.prog_depth self.current_prog_node pendingValues ∧
    values = currentValues ++ pendingValues ∧
    self.yielded.val + values.length ≤ self.length.val

end milhouse.progressive_tree
