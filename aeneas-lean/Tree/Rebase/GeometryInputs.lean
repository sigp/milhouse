import Tree.Rebase.Comparisons

open Aeneas Aeneas.Std Result

namespace milhouse.tree

/-- Shape compatibility and arithmetic bounds only where binary rebasing
actually checks them. Zero inputs accept every opposite shape; matching leaves
need no depth bound. Shared pointers omit all checks, and a node hash shortcut
omits both child geometry and the optional length-splitting shift. -/
def Tree.RebaseGeometry {T : Type} : Tree T → Tree T → RebaseLengths → Nat → Prop
  | .Leaf left, .PackedLeaf right, _, _ =>
      triomphe.arc.Arc.ptr_eq (.Leaf left : Tree T) (.PackedLeaf right) ≠ ok false
  | .Leaf left, .Node hash leftBase rightBase, _, _ =>
      triomphe.arc.Arc.ptr_eq (.Leaf left : Tree T) (.Node hash leftBase rightBase) ≠ ok false
  | .PackedLeaf left, .Leaf right, _, _ =>
      triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.Leaf right) ≠ ok false
  | .PackedLeaf left, .Node hash leftBase rightBase, _, _ =>
      triomphe.arc.Arc.ptr_eq (.PackedLeaf left : Tree T) (.Node hash leftBase rightBase) ≠ ok false
  | .Node hash left right, .Leaf base, _, _ =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Leaf base) ≠ ok false
  | .Node hash left right, .PackedLeaf base, _, _ =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.PackedLeaf base) ≠ ok false
  | .Node hash left right, .Node baseHash baseLeft baseRight, lengths, fullDepth =>
      triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Node baseHash baseLeft baseRight) = ok false →
      0 < fullDepth ∧ (¬ RebaseHashShortcutFor hash baseHash lengths →
        (lengths.isSome = true → fullDepth - 1 < UScalarTy.Usize.numBits) ∧
        left.RebaseGeometry baseLeft (rebaseLeftLengths lengths (fullDepth - 1)) (fullDepth - 1) ∧
        right.RebaseGeometry baseRight (rebaseRightLengths lengths (fullDepth - 1)) (fullDepth - 1))
  | _, _, _, _ => True

/-- Compatible whole-tree shapes and a global depth/shift bound imply the
weaker checks selected by the actual pointer, hash, and length decisions. -/
theorem Tree.rebaseGeometry_of_shape {T : Type} {orig base : Tree T}
    {factor : Option Std.Usize} {depth fullDepth : Nat} {lengths : RebaseLengths}
    (horig : orig.Shape factor depth) (hbase : base.Shape factor depth)
    (hdepth : depth ≤ fullDepth)
    (hbits : lengths.isSome = true → fullDepth ≤ UScalarTy.Usize.numBits) :
    orig.RebaseGeometry base lengths fullDepth := by
  induction orig generalizing base depth fullDepth lengths with
  | Leaf leaf | PackedLeaf leaf | Zero level =>
    cases base <;> simp only [Tree.RebaseGeometry]
    all_goals (cases horig; cases hbase)
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.RebaseGeometry]
    case Leaf | PackedLeaf => cases horig; cases hbase
    case Node baseHash baseLeft baseRight =>
      cases horig with
      | @node _ _ _ child _ hleft hright =>
        cases hbase with
        | node _ hbaseLeft hbaseRight =>
          refine fun _ => ⟨by omega, fun _ => ⟨fun hsome => by have := hbits hsome; omega, ?_, ?_⟩⟩
          · exact ihleft hleft hbaseLeft (by omega)
              (fun hsome => by
                have hparent : lengths.isSome = true := by simpa [rebaseLeftLengths] using hsome
                have := hbits hparent
                omega)
          · exact ihright hright hbaseRight (by omega)
              (fun hsome => by
                have hparent : lengths.isSome = true := by simpa [rebaseRightLengths] using hsome
                have := hbits hparent
                omega)

end milhouse.tree
