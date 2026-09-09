import Tree.HashCache
import Tree.Rebase.ContentsAction

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Combining the actual child actions preserves every content/depth-indexed
cache invariant. Rebuilt nodes retain the original root cache over unchanged
child contents; whole-base replacements inherit the base's valid caches. -/
theorem combineRebaseActions_preserves_caches {T : Type}
    (P : CacheSubject T → CacheHash → Prop)
    (origHash baseHash : CacheHash)
    (origLeft origRight baseLeft baseRight : Tree T)
    (leftAction rightAction : RebaseAction (Tree T)) (depth : Nat)
    (horig : P (.binary (depth + 1) (origLeft.elements ++ origRight.elements)) origHash)
    (hbase : (Tree.Node baseHash baseLeft baseRight).CachesOn P (depth + 1))
    (hleftContents : (applyRebaseAction origLeft leftAction).elements = origLeft.elements)
    (hrightContents : (applyRebaseAction origRight rightAction).elements = origRight.elements)
    (hleft : (applyRebaseAction origLeft leftAction).CachesOn P depth)
    (hright : (applyRebaseAction origRight rightAction).CachesOn P depth) :
    (applyRebaseAction (.Node origHash origLeft origRight)
      (combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
        leftAction rightAction)).CachesOn P (depth + 1) := by
  cases leftAction <;> cases rightAction <;>
    simp_all [combineRebaseActions, applyRebaseAction, Tree.CachesOn]

end milhouse.tree
