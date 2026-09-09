import Tree.HashCache
import Tree.Rebase.ContentsAction
import Tree.Rebase.Kind

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Combining the actual child actions preserves every content/depth-indexed
cache invariant. Whole-base replacement needs only the base caches. Other
actions retain the original root cache over unchanged child contents and
need validity only for the actual child results. -/
theorem combineRebaseActions_preserves_caches {T : Type}
    (P : CacheSubject T → CacheHash → Prop)
    (origHash baseHash : CacheHash)
    (origLeft origRight baseLeft baseRight : Tree T)
    (leftAction rightAction : RebaseAction (Tree T)) (depth : Nat)
    (horig : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      P (.binary (depth + 1) (origLeft.elements ++ origRight.elements)) origHash)
    (hbase : leftAction.kind.combine rightAction.kind = .equalReplace →
      (Tree.Node baseHash baseLeft baseRight).CachesOn P (depth + 1))
    (hleftContents : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origLeft leftAction).elements = origLeft.elements)
    (hrightContents : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origRight rightAction).elements = origRight.elements)
    (hleft : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origLeft leftAction).CachesOn P depth)
    (hright : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origRight rightAction).CachesOn P depth) :
    (applyRebaseAction (.Node origHash origLeft origRight)
      (combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
        leftAction rightAction)).CachesOn P (depth + 1) := by
  cases leftAction <;> cases rightAction <;>
    simp_all [RebaseAction.kind, RebaseKind.combine, combineRebaseActions, applyRebaseAction, Tree.CachesOn]

end milhouse.tree
