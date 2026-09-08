import Tree.Iter.Path

open Aeneas Aeneas.Std Result
open milhouse milhouse.tree

namespace milhouse.iter

/-- The first saved frame is the root from which the search started. -/
theorem Path.head_eq {T : Type} {packingDepth depth index : Nat}
    {root frame : tree.Tree T} {rest : _root_.List (tree.Tree T)}
    (h : Path packingDepth root depth index (frame :: rest)) : frame = root := by
  cases h <;> rfl

/-- A path ending at a saved node can continue with any search-path prefix
    rooted at that node. The current node is replaced by the continuation. -/
theorem Path.extend {T : Type} {packingDepth depth index : Nat}
    {root node : tree.Tree T} (completed rest : _root_.List (tree.Tree T))
    (h : Path packingDepth root depth index (completed ++ [node]))
    (htail : Path packingDepth node (depth - completed.length) index rest) :
    Path packingDepth root depth index (completed ++ rest) := by
  induction completed generalizing root depth with
  | nil =>
    have heq := h.head_eq
    subst root
    simpa using htail
  | cons frame completed ih =>
    change Path packingDepth root depth index (frame :: (completed ++ [node])) at h
    generalize hrest : completed ++ [node] = frames at h
    cases h with
    | stop => simp at hrest
    | left hash hbit tail =>
      rw [← hrest] at tail
      apply Path.left hash hbit
      apply ih tail
      simpa only [_root_.List.length_cons, Nat.add_sub_add_right] using htail
    | right hash hbit tail =>
      rw [← hrest] at tail
      apply Path.right hash hbit
      apply ih tail
      simpa only [_root_.List.length_cons, Nat.add_sub_add_right] using htail

/-- The natural-number routing bit agrees with the capacity-based slot model. -/
theorem routing_left_iff {factor : Option Std.Usize} {packingDepth : Nat}
    (hpacking : leafCapacity factor = 2 ^ packingDepth) (depth index : Nat) :
    index / 2 ^ (depth + packingDepth) % 2 = 0 ↔
      index % subtreeCapacity factor (depth + 1) < subtreeCapacity factor depth := by
  have hchild : subtreeCapacity factor depth = 2 ^ (depth + packingDepth) := by
    simp [subtreeCapacity, hpacking, pow_add, Nat.mul_comm]
  have hparent : subtreeCapacity factor (depth + 1) = 2 ^ (depth + packingDepth) * 2 := by
    simp [subtreeCapacity, hpacking, pow_add, pow_succ, Nat.mul_comm, Nat.mul_left_comm]
  rw [hchild, hparent, ← Nat.mod_mul_right_div_self]
  exact Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)

/-- The current frame has the remaining binary depth and the same selected
    slot as the root. These facts follow from shape and the recorded path;
    they are not assumptions about the iterator's output. -/
theorem Path.top {T : Type} {factor : Option Std.Usize} {packingDepth depth index : Nat}
    {root node : tree.Tree T} (completed : _root_.List (tree.Tree T))
    (hpacking : leafCapacity factor = 2 ^ packingDepth)
    (hshape : root.Shape factor depth)
    (h : Path packingDepth root depth index (completed ++ [node])) :
    node.Shape factor (depth - completed.length) ∧
      root.slot factor depth index = node.slot factor (depth - completed.length) index := by
  induction completed generalizing root depth with
  | nil =>
    have heq := h.head_eq
    subst root
    constructor
    · simpa using hshape
    · rfl
  | cons frame completed ih =>
    change Path packingDepth root depth index (frame :: (completed ++ [node])) at h
    generalize hrest : completed ++ [node] = frames at h
    cases h with
    | stop => simp at hrest
    | @left left right child index rest hash hbit tail =>
      rw [← hrest] at tail
      cases hshape with
      | node _ hleft hright =>
        obtain ⟨hnode, hslot⟩ := ih hleft tail
        constructor
        · simpa only [_root_.List.length_cons, Nat.add_sub_add_right] using hnode
        · rw [Tree.slot, if_pos ((routing_left_iff hpacking child index).mp hbit), hslot]
          simp only [_root_.List.length_cons, Nat.add_sub_add_right]
    | @right left right child index rest hash hbit tail =>
      rw [← hrest] at tail
      cases hshape with
      | node _ hleft hright =>
        obtain ⟨hnode, hslot⟩ := ih hright tail
        constructor
        · simpa only [_root_.List.length_cons, Nat.add_sub_add_right] using hnode
        · rw [Tree.slot, if_neg (fun hroute => hbit ((routing_left_iff hpacking child index).mpr hroute)), hslot]
          simp only [_root_.List.length_cons, Nat.add_sub_add_right]

end milhouse.iter
