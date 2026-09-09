import Tree.HashCache.Cleared
import Tree.Rebase.ContentsAction
import Tree.Rebase.CacheInputs
import Tree.Rebase.HashInputs

open Aeneas Aeneas.Std Result

namespace milhouse

/-- A pair of binary hash inputs at a common depth. -/
abbrev BinaryHashInputPair (T : Type) := Nat × _root_.List T × _root_.List T

/-- Collision soundness restricted to a finite collection of input pairs.
Only equal-length inputs with an equal nonzero reference hash must agree.
This is a property of the mathematical reference function, not an axiom or
a model of the Rust hash computation. -/
def BinaryHashCollisionSoundOn {T : Type} (reference : CacheSubject T → CacheHash)
    (pairs : _root_.List (BinaryHashInputPair T)) : Prop :=
  ∀ pair ∈ pairs, pair.2.1.length = pair.2.2.length →
    reference (.binary pair.1 pair.2.1) ≠ Array.repeat 32#usize 0#u8 →
    reference (.binary pair.1 pair.2.1) = reference (.binary pair.1 pair.2.2) →
    pair.2.1 = pair.2.2

theorem BinaryHashCollisionSoundOn.mono {T : Type} {reference : CacheSubject T → CacheHash}
    {pairs selected : _root_.List (BinaryHashInputPair T)}
    (hsound : BinaryHashCollisionSoundOn reference pairs)
    (hselected : ∀ pair ∈ selected, pair ∈ pairs) :
    BinaryHashCollisionSoundOn reference selected :=
  fun pair hpair => hsound pair (hselected pair hpair)

theorem BinaryHashCollisionSoundOn.nil {T : Type} (reference : CacheSubject T → CacheHash) :
    BinaryHashCollisionSoundOn reference [] := by
  simp [BinaryHashCollisionSoundOn]

theorem CacheValidFor.eq_reference_of_nonzero {T : Type}
    {reference : CacheSubject T → CacheHash} {subject : CacheSubject T} {cached : CacheHash}
    (hvalid : CacheValidFor reference subject cached)
    (hnonzero : cached ≠ Array.repeat 32#usize 0#u8) : cached = reference subject :=
  hvalid.resolve_left hnonzero

namespace tree

/-- Binary inputs at selected nonzero equal-hash, equal-length shortcuts.
Pointer sharing omits the complete subtree; taking a hash shortcut includes
only its root pair. Otherwise the scope follows both corresponding children.
Input density connects these sequence lengths to operational Rust metadata. -/
noncomputable def Tree.rebaseHashInputs {T : Type} (orig base : Tree T) (depth : Nat) :
    _root_.List (BinaryHashInputPair T) := by
  classical
  exact match orig, base with
  | .Node hash left right, .Node baseHash baseLeft baseRight =>
    if triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Node baseHash baseLeft baseRight) = ok false then
      if RebaseHashShortcut hash baseHash (left.elements ++ right.elements).length
          (baseLeft.elements ++ baseRight.elements).length then
        [(depth, left.elements ++ right.elements, baseLeft.elements ++ baseRight.elements)]
      else left.rebaseHashInputs baseLeft (depth - 1) ++ right.rebaseHashInputs baseRight (depth - 1)
    else []
  | _, _ => []

/-- Cleared original caches require no collision assumption against any base. -/
theorem Tree.rebaseHashInputs_eq_nil_of_cleared {T : Type}
    (orig base : Tree T) (depth : Nat) (hclear : orig.CachesCleared) :
    orig.rebaseHashInputs base depth = [] := by
  induction orig generalizing base depth with
  | Leaf leaf => rfl
  | PackedLeaf leaf => rfl
  | Zero level => rfl
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.rebaseHashInputs]
    rename_i baseHash baseLeft baseRight
    simp [hclear.1, RebaseHashShortcut, Array.repeat, ihleft baseLeft (depth - 1) hclear.2.1,
      ihright baseRight (depth - 1) hclear.2.2]

/-- Cleared original caches cannot take a hash shortcut. Their operational
agreement therefore needs no validity invariant on the base or reference law. -/
theorem Tree.cachedHashesAgree_of_cleared {T : Type}
    (orig base : Tree T) (hclear : orig.CachesCleared) : orig.CachedHashesAgree base := by
  induction orig generalizing base with
  | Leaf leaf => cases base <;> trivial
  | PackedLeaf leaf => cases base <;> trivial
  | Zero level => cases base <;> trivial
  | Node hash left right ihleft ihright =>
    cases base <;> simp only [Tree.CachedHashesAgree]
    rename_i baseHash baseLeft baseRight
    intro _
    refine ⟨?_, fun _ => ⟨ihleft baseLeft hclear.2.1, ihright baseRight hclear.2.2⟩⟩
    intro hshortcut
    apply False.elim
    apply hshortcut.1
    simp [hclear.1, Array.repeat]

/-- Original validity at reached hash shortcuts, validity of selected base
caches, and collision soundness on the corresponding finite hash inputs
establish the operational shortcut law. No validity is required for original
leaf caches or roots whose hash shortcut is not taken. Depths are explicit;
no shape, element soundness, packing, or execution law is used. -/
theorem Tree.cachedHashesAgree_of_valid_caches {T : Type}
    (inst : core.cmp.PartialEq T T) (reference : CacheSubject T → CacheHash)
    (orig base : Tree T) (depth : Nat)
    (horig : orig.RebaseHashCachesOn (CacheValidFor reference) base depth)
    (hbase : orig.RebaseBaseCachesOn inst (CacheValidFor reference) base depth)
    (hcollisions : BinaryHashCollisionSoundOn reference (orig.rebaseHashInputs base depth)) :
    orig.CachedHashesAgree base := by
  induction orig generalizing base depth with
  | Leaf leaf => cases base <;> trivial
  | PackedLeaf leaf => cases base <;> trivial
  | Zero level => cases base <;> trivial
  | Node hash left right ihleft ihright =>
    cases base with
    | Leaf leaf => trivial
    | PackedLeaf leaf => trivial
    | Zero level => trivial
    | Node baseHash baseLeft baseRight =>
      intro hpointer
      refine ⟨?_, ?_⟩
      · intro hshortcut
        have hbaseCache := hbase.base_of_equal_replace
          (Tree.rebaseKind_of_hash_shortcut inst _ _ _ _ _ _ hpointer hshortcut)
        have hguard := hshortcut
        obtain ⟨hnonzero, hequal, hlength⟩ := hshortcut
        have hnonzero' : hash ≠ Array.repeat 32#usize 0#u8 := by
          intro hzero
          apply hnonzero
          simp [hzero, Array.repeat]
        have hhash : hash = baseHash := Subtype.ext hequal
        have horigRef := ((horig hpointer).1 hguard).eq_reference_of_nonzero hnonzero'
        have hbaseRef := hbaseCache.1.eq_reference_of_nonzero (by
          intro hzero
          exact hnonzero' (hhash.trans hzero))
        apply hcollisions (depth, left.elements ++ right.elements,
          baseLeft.elements ++ baseRight.elements)
        · simp only [Tree.rebaseHashInputs, hpointer, ↓reduceIte, if_pos hguard, List.mem_singleton]
        · exact hlength
        · simpa only [← horigRef] using hnonzero'
        · exact horigRef.symm.trans (hhash.trans hbaseRef)
      · intro hdescend
        have hbaseChildren := hbase.children hpointer hdescend
        have hchildren : BinaryHashCollisionSoundOn reference
            (left.rebaseHashInputs baseLeft (depth - 1) ++
              right.rebaseHashInputs baseRight (depth - 1)) := by
          simpa only [Tree.rebaseHashInputs, hpointer, ↓reduceIte, if_neg hdescend] using hcollisions
        exact ⟨ihleft baseLeft (depth - 1) ((horig hpointer).2 hdescend).1 hbaseChildren.1
            (hchildren.mono (fun pair hpair => List.mem_append_left _ hpair)),
          ihright baseRight (depth - 1) ((horig hpointer).2 hdescend).2 hbaseChildren.2
            (hchildren.mono (fun pair hpair => List.mem_append_right _ hpair))⟩

end tree
end milhouse
