import Tree.Rebase.Soundness
import Tree.Rebase.ComparisonInputs

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Content soundness only at comparisons selected by the supplied optional
lengths and full depth. Positive leaf equality and all-false packed `ne` calls
must identify equal values. A reached hash shortcut must identify equal
sequences; otherwise only the corresponding child inputs need laws. Pointer
shortcuts and nonpositive node depths omit every semantic obligation. -/
def Tree.RebaseContentInputs {T : Type} (inst : core.cmp.PartialEq T T) :
    Tree T → Tree T → RebaseLengths → Nat → Prop
  | .Leaf left, .Leaf right, _, _ =>
      triomphe.arc.Arc.ptr_eq (.Leaf left : Tree T) (.Leaf right) = ok false →
      triomphe.arc.Arc.ptr_eq left.value right.value = ok false →
      inst.eq left.value right.value = ok true → left.value = right.value
  | .PackedLeaf left, .PackedLeaf right, _, _ =>
      triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.PackedLeaf right) = ok false →
      left.values.val.length = right.values.val.length →
      milhouse_models.NeSoundIfAllFalse inst (left.values.val.zip right.values.val)
  | .Node hash left right, .Node baseHash baseLeft baseRight, lengths, fullDepth =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Node baseHash baseLeft baseRight) = ok false →
      0 < fullDepth →
      (RebaseHashShortcutFor hash baseHash lengths →
        left.elements ++ right.elements = baseLeft.elements ++ baseRight.elements) ∧
      (¬ RebaseHashShortcutFor hash baseHash lengths →
        left.RebaseContentInputs inst baseLeft (rebaseLeftLengths lengths (fullDepth - 1)) (fullDepth - 1) ∧
        right.RebaseContentInputs inst baseRight (rebaseRightLengths lengths (fullDepth - 1)) (fullDepth - 1))
  | _, _, _, _ => True

/-- Accurate dense metadata supplies the actual comparison scope from the
earlier element/hash laws stated at materialized lengths. This adapter needs
layout; the operational content theorem does not. -/
theorem Tree.rebaseContentInputs_of_dense {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    {orig base : Tree T} {depth origLength baseLength fullDepth : Nat}
    (hdepth : fullDepth = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength) (hbase : DenseTree factor base depth baseLength)
    (hequality : orig.RebaseEqualitySound ValueInst.corecmpPartialEqInst base)
    (hhashes : orig.CachedHashesAgree base) :
    orig.RebaseContentInputs ValueInst.corecmpPartialEqInst base (some (origLength, baseLength)) fullDepth := by
  induction orig generalizing base depth origLength baseLength fullDepth with
  | Leaf leaf | PackedLeaf leaf | Zero level =>
    cases base <;> simp only [Tree.RebaseContentInputs]
    all_goals exact hequality
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.RebaseContentInputs]
    case Node baseHash baseLeft baseRight =>
      intro hpointer _
      have horigLength : (left.elements ++ right.elements).length = origLength := horig.elements_length
      have hbaseLength : (baseLeft.elements ++ baseRight.elements).length = baseLength := hbase.elements_length
      have hguard : RebaseHashShortcutFor hash baseHash (some (origLength, baseLength)) ↔
          RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
            (baseLeft.elements ++ baseRight.elements).length := by
        simp only [RebaseHashShortcutFor, RebaseHashShortcut, horigLength, hbaseLength, Option.elim_some]
      refine ⟨fun hshortcut => (hhashes hpointer).1 (hguard.mp hshortcut), fun hdescend => ?_⟩
      have hdescend' := fun hshortcut => hdescend (hguard.mpr hshortcut)
      obtain ⟨child, hchild⟩ : ∃ child, depth = child + 1 := by
        have hshape := horig.shape
        cases hshape with
        | @node _ _ _ child _ _ _ => exact ⟨child, rfl⟩
      subst depth
      have hcapacity : 2 ^ (fullDepth - 1) = subtreeCapacity factor child := by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        congr 1
        omega
      obtain ⟨hleft, hright⟩ := horig.split_node
      obtain ⟨hbaseLeft, hbaseRight⟩ := hbase.split_node
      constructor
      · simp only [rebaseLeftLengths, Option.map_some, hcapacity]
        exact ihleft (by omega) hleft hbaseLeft
          (hequality hpointer hdescend').1 ((hhashes hpointer).2 hdescend').1
      · simp only [rebaseRightLengths, Option.map_some, hcapacity]
        exact ihright (by omega) hright hbaseRight
          (hequality hpointer hdescend').2 ((hhashes hpointer).2 hdescend').2

end milhouse.tree
