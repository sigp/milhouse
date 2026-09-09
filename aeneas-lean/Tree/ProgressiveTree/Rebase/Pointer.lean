import Tree.Rebase.Pointer
import Tree.ProgressiveTree.Rebase.Validity
import Tree.ProgressiveTree.Rebase.Success

open Aeneas Aeneas.Std Result

namespace milhouse.progressive_tree

/-- The recursive pointer shortcut returns the shared base without reading
length/depth metadata, caches, or any element. -/
theorem ProgressiveTree.rebase_on_recursive_of_ptr_eq {T : Type} (ValueInst : Value T)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize) (depth : Std.U32)
    (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    ProgressiveTree.rebase_on_recursive ValueInst orig base origLength baseLength depth =
      ok (.Ok base) := by
  rw [ProgressiveTree.rebase_on_recursive, hpointer]
  rfl

theorem ProgressiveTree.rebase_on_of_ptr_eq {T : Type} (ValueInst : Value T)
    (orig base : ProgressiveTree T) (origLength baseLength : Std.Usize)
    (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    ProgressiveTree.rebase_on ValueInst orig base origLength baseLength = ok (.Ok base) :=
  ProgressiveTree.rebase_on_recursive_of_ptr_eq ValueInst orig base origLength baseLength 0#u32 hpointer

theorem ProgressiveTree.rebaseComparisons_of_ptr_eq {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : ProgressiveTree T) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseComparisons inst base := by
  cases orig <;> cases base <;> simp [ProgressiveTree.RebaseComparisons, hpointer]

theorem ProgressiveTree.rebaseEqualitySound_of_ptr_eq {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : ProgressiveTree T) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseEqualitySound inst base := by
  cases orig <;> cases base <;> simp [ProgressiveTree.RebaseEqualitySound, hpointer]

theorem ProgressiveTree.cachedHashesAgree_of_ptr_eq {T : Type}
    (orig base : ProgressiveTree T) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.CachedHashesAgree base := by
  cases orig <;> cases base <;> simp [ProgressiveTree.CachedHashesAgree, hpointer]

theorem ProgressiveTree.rebaseHashInputs_eq_nil_of_ptr_eq {T : Type}
    (orig base : ProgressiveTree T) (depth : Nat)
    (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.rebaseHashInputs base depth = [] := by
  cases orig <;> cases base <;> simp [ProgressiveTree.rebaseHashInputs, hpointer]

end milhouse.progressive_tree
