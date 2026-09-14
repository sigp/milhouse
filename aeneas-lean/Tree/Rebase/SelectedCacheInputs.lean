import Tree.Rebase.SelectedKind
import Tree.Rebase.CacheInputs
import Tree.Rebase.OriginalCaches

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.tree

/-- Stored cache laws selected by the supplied-metadata action category.
No-ops require the original caches; whole-base replacement requires only
base caches; rebuilding requires the original root and the selected child
caches. Cache-subject depth is independent of the supplied machine depth.
This predicate contains no output tree or assumed execution. -/
def Tree.RebaseCacheInputs {T : Type} (inst : core.cmp.PartialEq T T)
    (P : CacheSubject T → CacheHash → Prop) (orig base : Tree T)
    (lengths : RebaseLengths) (fullDepth depth : Nat) : Prop :=
  match orig.rebaseKindFor inst base lengths fullDepth with
  | .equalReplace => base.CachesOn P depth
  | .notEqualReplace =>
      match orig, base with
      | .Node hash left right, .Node _ baseLeft baseRight =>
          P (.binary depth (left.elements ++ right.elements)) hash ∧
            left.RebaseCacheInputs inst P baseLeft (rebaseLeftLengths lengths (fullDepth - 1))
              (fullDepth - 1) (depth - 1) ∧
            right.RebaseCacheInputs inst P baseRight (rebaseRightLengths lengths (fullDepth - 1))
              (fullDepth - 1) (depth - 1)
      | _, _ => True
  | .notEqualNoop | .equalNoop => orig.CachesOn P depth

/-- At accurate dense metadata, the combined general scope is equivalent
to the existing retained-original and imported-base cache scopes. -/
theorem Tree.rebaseCacheInputs_iff_of_dense {T : Type} (ValueInst : Value T)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : PackingLayout ValueInst factor packingDepth)
    (P : CacheSubject T → CacheHash → Prop)
    {orig base : Tree T} {depth origLength baseLength fullDepth : Nat}
    (hdepth : fullDepth = depth + packingDepth.val)
    (horig : DenseTree factor orig depth origLength) (hbase : DenseTree factor base depth baseLength) :
    orig.RebaseCacheInputs ValueInst.corecmpPartialEqInst P base (some (origLength, baseLength)) fullDepth depth ↔
      orig.RebaseOrigCachesOn ValueInst.corecmpPartialEqInst P base depth ∧
        orig.RebaseBaseCachesOn ValueInst.corecmpPartialEqInst P base depth := by
  induction orig generalizing base depth origLength baseLength fullDepth with
  | Leaf leaf | PackedLeaf leaf | Zero level =>
    rw [Tree.RebaseCacheInputs.eq_def, Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def,
      Tree.rebaseKindFor_eq_of_dense ValueInst hlayout hdepth horig hbase]
    cases base <;> split <;> simp_all
  | Node hash left right ihleft ihright =>
    have hkind := Tree.rebaseKindFor_eq_of_dense ValueInst hlayout hdepth horig hbase
    cases base with
    | Leaf leaf | PackedLeaf leaf | Zero level =>
      rw [Tree.RebaseCacheInputs.eq_def, Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def, hkind]
      split <;> simp_all
    | Node baseHash baseLeft baseRight =>
      obtain ⟨child, hchild⟩ : ∃ child, depth = child + 1 := by
        have hshape := horig.shape
        cases hshape with
        | @node _ _ _ child _ _ _ => exact ⟨child, rfl⟩
      subst depth
      have hcapacity : 2 ^ (fullDepth - 1) = subtreeCapacity factor child := by
        rw [hlayout.subtreeCapacity_eq_two_pow]
        congr 1
        omega
      rw [Tree.RebaseCacheInputs.eq_def, Tree.RebaseOrigCachesOn.eq_def, Tree.RebaseBaseCachesOn.eq_def, hkind]
      split <;> rename_i hcase
      · simp only [hcase, true_and]
      · simp only [hcase, rebaseLeftLengths, rebaseRightLengths, Option.map_some, hcapacity, Nat.add_sub_cancel]
        rw [ihleft (by omega) horig.split_node.1 hbase.split_node.1,
          ihright (by omega) horig.split_node.2 hbase.split_node.2]
        tauto
      · simp only [hcase, and_true]
      · simp only [hcase, and_true]

end milhouse.tree
