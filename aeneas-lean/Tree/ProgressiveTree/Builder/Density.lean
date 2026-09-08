import Tree.ProgressiveTree.Builder.Spine

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.progressive_tree

/-- Completed builder subtrees fill consecutive progressive layers. -/
def FullLayers {T : Type} (factor : Option Std.Usize) :
    Nat → _root_.List (tree.Tree T) → Prop
  | _, [] => True
  | depth, left :: rest =>
    DenseTree factor left (2 * depth) (subtreeCapacity factor (2 * depth)) ∧
      FullLayers factor (depth + 1) rest

theorem FullLayers.append {T : Type} {factor : Option Std.Usize}
    {depth : Nat} {left right : _root_.List (tree.Tree T)}
    (hleft : FullLayers factor depth left)
    (hright : FullLayers factor (depth + left.length) right) :
    FullLayers factor depth (left ++ right) := by
  induction left generalizing depth with
  | nil => simpa using hright
  | cons head tail ih =>
    exact ⟨hleft.1, ih hleft.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright)⟩

/-- The completed forest's values occupy exactly the interval between its
    first layer and the start of the next unfinished layer. -/
theorem FullLayers.elements_length {T : Type} {factor : Option Std.Usize}
    {depth : Nat} {subtrees : _root_.List (tree.Tree T)}
    (hfull : FullLayers factor depth subtrees) :
    progressiveCapacity factor depth + (subtrees.flatMap tree.Tree.elements).length =
      progressiveCapacity factor (depth + subtrees.length) := by
  induction subtrees generalizing depth with
  | nil => simp
  | cons head tail ih =>
    have htail := ih hfull.2
    rw [progressiveCapacity_succ] at htail
    simpa [_root_.List.flatMap_cons, hfull.1.elements_length,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Prepending completed layers to a dense suffix preserves density. This
    applies both to final partial layers and to an empty terminating suffix. -/
theorem ProgressiveTree.ofSubtrees_dense {T : Type} {factor : Option Std.Usize}
    {depth length : Nat} (subtrees : _root_.List (tree.Tree T)) (suffix : ProgressiveTree T)
    (hfull : FullLayers factor depth subtrees)
    (hsuffix : suffix.Dense factor (depth + subtrees.length) length) :
    (ProgressiveTree.ofSubtrees subtrees suffix).Dense factor depth
      ((subtrees.flatMap tree.Tree.elements).length + length) := by
  induction subtrees generalizing depth with
  | nil => simpa [ProgressiveTree.ofSubtrees] using hsuffix
  | cons head tail ih =>
    have htail := ih hfull.2 (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsuffix)
    have hnode := ProgressiveTree.Dense.node (Array.repeat 32#usize 0#u8)
      hfull.1 htail (fun _ => rfl)
    simpa [ProgressiveTree.ofSubtrees, _root_.List.flatMap_cons,
      hfull.1.elements_length, Nat.add_assoc] using hnode

/-- Actual spine assembly is dense when its completed completed is full and its
    final binary subtree is dense at the next layer. No machine or packing
    assumptions are added by assembly. -/
theorem ProgressiveTree.from_spine_subtrees_dense_last {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {completed : _root_.List (tree.Tree T)} {last : tree.Tree T}
    {lastLength : Nat} {subtrees : alloc.vec.Vec (tree.Tree T)} {output : ProgressiveTree T}
    (hsubtrees : subtrees.val = completed ++ [last])
    (hfull : FullLayers factor 0 completed)
    (hlast : DenseTree factor last (2 * completed.length) lastLength)
    (hassemble : ProgressiveTree.from_spine_subtrees ValueInst subtrees = ok output) :
    output.Dense factor 0 ((completed.flatMap tree.Tree.elements).length + lastLength) := by
  rw [ProgressiveTree.from_spine_subtrees_eq ValueInst subtrees hassemble, hsubtrees]
  have hsuffix : (ProgressiveTree.ofSubtrees [last] .ProgressiveZero).Dense
      factor completed.length lastLength := by
    simpa [ProgressiveTree.ofSubtrees] using
      ProgressiveTree.Dense.node (Array.repeat 32#usize 0#u8) hlast
        (ProgressiveTree.Dense.zero factor (completed.length + 1)) (by simp)
  have hresult := ProgressiveTree.ofSubtrees_dense completed
    (ProgressiveTree.ofSubtrees [last] .ProgressiveZero) hfull (by simpa using hsuffix)
  simpa [ProgressiveTree.ofSubtrees, _root_.List.foldr_append] using hresult

end milhouse.progressive_tree
