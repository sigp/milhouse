import Tree.HashCache.Collisions
import Tree.Rebase.Comparisons
import Tree.Rebase.Soundness

open Aeneas Aeneas.Std Result

namespace milhouse.tree

/-- The outer pointer shortcut succeeds before any shape, depth, length,
hash-cache, or element-comparison check. -/
theorem Tree.rebase_on_of_ptr_eq {T : Type} (ValueInst : Value T)
    (orig base : Tree T) (lengths : Option (utils.Length × utils.Length)) (fullDepth : Std.Usize)
    (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    Tree.rebase_on ValueInst orig base lengths fullDepth = ok (.Ok .EqualNoop) := by
  rw [Tree.rebase_on, hpointer]
  rfl

theorem Tree.rebaseComparisons_of_ptr_eq {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : Tree T) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseComparisons inst base := by
  cases orig <;> cases base <;> simp [Tree.RebaseComparisons, hpointer]

theorem Tree.rebaseEqualitySound_of_ptr_eq {T : Type} (inst : core.cmp.PartialEq T T)
    (orig base : Tree T) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.RebaseEqualitySound inst base := by
  cases orig <;> cases base <;> simp [Tree.RebaseEqualitySound, hpointer]

theorem Tree.cachedHashesAgree_of_ptr_eq {T : Type}
    (orig base : Tree T) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.CachedHashesAgree base := by
  cases orig <;> cases base <;> simp [Tree.CachedHashesAgree, hpointer]

/-- Shared subtrees contribute no reference collision obligations, including
obligations about any of their descendants. -/
theorem Tree.rebaseHashInputs_eq_nil_of_ptr_eq {T : Type}
    (orig base : Tree T) (depth : Nat) (hpointer : triomphe.arc.Arc.ptr_eq orig base = ok true) :
    orig.rebaseHashInputs base depth = [] := by
  cases orig <;> cases base <;> simp [Tree.rebaseHashInputs, hpointer]

end milhouse.tree
