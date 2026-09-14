import Tree.Rebase.Kind
import Tree.Rebase.ComparisonInputs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Input-based action category at the supplied optional lengths and full
depth. Hash guards and recursive splits use this metadata, independently of
stored contents or geometry. As with `rebaseKind`, categories assigned to
unsuccessful computations are irrelevant to the reflection theorem. -/
noncomputable def Tree.rebaseKindFor {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : Tree T) (lengths : RebaseLengths) (fullDepth : Nat) : RebaseKind := by
  classical
  exact if triomphe.arc.Arc.ptr_eq orig base = ok false then
    match orig, base with
    | .Leaf left, .Leaf right =>
        if triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq inst left.value right.value = ok true
        then .equalReplace else .notEqualNoop
    | .PackedLeaf left, .PackedLeaf right =>
        if milhouse_models.vec_eq inst left.values right.values = ok true
        then .equalReplace else .notEqualNoop
    | .Zero left, .Zero right => if left = right then .equalReplace else .notEqualNoop
    | .Node hash left right, .Node baseHash baseLeft baseRight =>
        if RebaseHashShortcutFor hash baseHash lengths then .equalReplace
        else (left.rebaseKindFor inst baseLeft (rebaseLeftLengths lengths (fullDepth - 1)) (fullDepth - 1)).combine
          (right.rebaseKindFor inst baseRight (rebaseRightLengths lengths (fullDepth - 1)) (fullDepth - 1))
    | _, _ => .notEqualNoop
  else .equalNoop

/-- Pointer sharing selects a no-op independently of supplied metadata. -/
theorem Tree.rebaseKindFor_of_ptr_eq {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : Tree T) (lengths : RebaseLengths) (fullDepth : Nat)
    (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.rebaseKindFor inst base lengths fullDepth = .equalNoop := by
  rw [Tree.rebaseKindFor.eq_def]
  simp [hpointer]

/-- A selected hash shortcut imports the base regardless of its stored
contents; the separate content law accounts for semantic soundness. -/
theorem Tree.rebaseKindFor_of_hash_shortcut {T : Type} (inst : core.cmp.PartialEq T T)
    (hash baseHash : CacheHash) (left right baseLeft baseRight : Tree T)
    (lengths : RebaseLengths) (fullDepth : Nat)
    (hpointer : triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T)
      (.Node baseHash baseLeft baseRight) = ok false)
    (hshortcut : RebaseHashShortcutFor hash baseHash lengths) :
    (Tree.Node hash left right).rebaseKindFor inst (.Node baseHash baseLeft baseRight)
      lengths fullDepth = .equalReplace := by
  rw [Tree.rebaseKindFor.eq_def]
  simp only [hpointer, ↓reduceIte, if_pos hshortcut]

/-- Rejected pointer and hash shortcuts expose the ordered child categories
at the exact split metadata, including the `none` length branch. -/
theorem Tree.rebaseKindFor_of_descend {T : Type} (inst : core.cmp.PartialEq T T)
    (hash baseHash : CacheHash) (left right baseLeft baseRight : Tree T)
    (lengths : RebaseLengths) (fullDepth : Nat)
    (hpointer : triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T)
      (.Node baseHash baseLeft baseRight) = ok false)
    (hdescend : ¬ RebaseHashShortcutFor hash baseHash lengths) :
    (Tree.Node hash left right).rebaseKindFor inst (.Node baseHash baseLeft baseRight) lengths fullDepth =
      (left.rebaseKindFor inst baseLeft (rebaseLeftLengths lengths (fullDepth - 1)) (fullDepth - 1)).combine
        (right.rebaseKindFor inst baseRight (rebaseRightLengths lengths (fullDepth - 1)) (fullDepth - 1)) := by
  rw [Tree.rebaseKindFor.eq_def]
  simp only [hpointer, ↓reduceIte, if_neg hdescend]

/-- Accurate dense metadata identifies the general classifier with the
existing content-based classifier. Layout is needed only by this adapter. -/
theorem Tree.rebaseKindFor_eq_of_dense {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : Tree T} {depth origLength baseLength fullDepth : Nat}
    (hdepth : fullDepth = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength) (hbase : DenseTree factor base depth baseLength) :
    orig.rebaseKindFor ValueInst.corecmpPartialEqInst base (some (origLength, baseLength)) fullDepth =
      orig.rebaseKind ValueInst.corecmpPartialEqInst base := by
  induction orig generalizing base depth origLength baseLength fullDepth with
  | Leaf leaf | PackedLeaf leaf | Zero level =>
    cases base <;> rw [Tree.rebaseKindFor.eq_def, Tree.rebaseKind.eq_def]
  | Node hash left right ihleft ihright =>
    cases base with
    | Leaf leaf | PackedLeaf leaf | Zero level =>
      rw [Tree.rebaseKindFor.eq_def, Tree.rebaseKind.eq_def]
    | Node baseHash baseLeft baseRight =>
      have horigLength : (left.elements ++ right.elements).length = origLength := horig.elements_length
      have hbaseLength : (baseLeft.elements ++ baseRight.elements).length = baseLength := hbase.elements_length
      have hguard : RebaseHashShortcutFor hash baseHash (some (origLength, baseLength)) ↔
          RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
            (baseLeft.elements ++ baseRight.elements).length := by
        simp only [RebaseHashShortcutFor, RebaseHashShortcut, horigLength, hbaseLength, Option.elim_some]
      obtain ⟨child, hchild⟩ : ∃ child, depth = child + 1 := by
        have hshape := horig.shape
        cases hshape with
        | @node _ _ _ child _ _ _ => exact ⟨child, rfl⟩
      subst depth
      have hcapacity : 2 ^ (fullDepth - 1) = subtreeCapacity factor child := by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        congr 1
        omega
      rw [Tree.rebaseKindFor.eq_def, Tree.rebaseKind.eq_def]
      dsimp only
      rw [propext hguard]
      split
      · split
        · rfl
        · simp only [rebaseLeftLengths, rebaseRightLengths, Option.map_some, hcapacity]
          rw [ihleft (by omega) horig.split_node.1 hbase.split_node.1,
            ihright (by omega) horig.split_node.2 hbase.split_node.2]
      · rfl

end milhouse.tree
