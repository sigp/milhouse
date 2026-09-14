import Tree.HashCache
import Tree.Rebase.ContentsAction
import Tree.Rebase.Kind

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- At any cache-subject depth, including zero, the combined action either
imports the full base or retains the original root and both child results.
Content laws identify the retained root's subject only; no geometry is used. -/
theorem combineRebaseActions_cache_iff {T : Type}
    (P : CacheSubject T → CacheHash → Prop)
    (origHash baseHash : CacheHash) (origLeft origRight baseLeft baseRight : Tree T)
    (leftAction rightAction : RebaseAction (Tree T)) (depth : Nat)
    (hleftContents : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origLeft leftAction).elements = origLeft.elements)
    (hrightContents : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origRight rightAction).elements = origRight.elements) :
    (applyRebaseAction (.Node origHash origLeft origRight)
      (combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
        leftAction rightAction)).CachesOn P depth ↔
      if leftAction.kind.combine rightAction.kind = .equalReplace then
        (Tree.Node baseHash baseLeft baseRight).CachesOn P depth
      else P (.binary depth (origLeft.elements ++ origRight.elements)) origHash ∧
        (applyRebaseAction origLeft leftAction).CachesOn P (depth - 1) ∧
          (applyRebaseAction origRight rightAction).CachesOn P (depth - 1) := by
  cases leftAction <;> cases rightAction <;>
    simp_all [RebaseAction.kind, RebaseKind.combine, combineRebaseActions, applyRebaseAction, Tree.CachesOn]

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

/-- Cache validity of the combined result exposes exactly the cache inputs
used by its branch. Whole-base replacement supplies base validity; every
other branch supplies the retained root and both actual child results.
The content laws only identify the retained root's logical subject. -/
theorem combineRebaseActions_cache_inputs {T : Type}
    (P : CacheSubject T → CacheHash → Prop)
    (origHash baseHash : CacheHash) (origLeft origRight baseLeft baseRight : Tree T)
    (leftAction rightAction : RebaseAction (Tree T)) (depth : Nat)
    (hleftContents : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origLeft leftAction).elements = origLeft.elements)
    (hrightContents : leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      (applyRebaseAction origRight rightAction).elements = origRight.elements)
    (hcache : (applyRebaseAction (.Node origHash origLeft origRight)
      (combineRebaseActions origHash baseHash origLeft origRight baseLeft baseRight
        leftAction rightAction)).CachesOn P (depth + 1)) :
    (leftAction.kind.combine rightAction.kind = .equalReplace →
      (Tree.Node baseHash baseLeft baseRight).CachesOn P (depth + 1)) ∧
    (leftAction.kind.combine rightAction.kind ≠ .equalReplace →
      P (.binary (depth + 1) (origLeft.elements ++ origRight.elements)) origHash ∧
        (applyRebaseAction origLeft leftAction).CachesOn P depth ∧
          (applyRebaseAction origRight rightAction).CachesOn P depth) := by
  cases leftAction <;> cases rightAction <;>
    simp_all [RebaseAction.kind, RebaseKind.combine, combineRebaseActions, applyRebaseAction, Tree.CachesOn]

end milhouse.tree
