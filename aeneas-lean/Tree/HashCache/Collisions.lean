import Tree.HashCache.Cleared
import Tree.Rebase.ContentsAction

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

/-- Corresponding binary-node inputs for which the original cache is populated.
The finite collection omits leaf comparisons, mismatched constructors, and
zero-cache nodes. It contains no inputs from unrelated trees. Children remain
included to supply the recursive cache law used by the existing rebase proof. -/
noncomputable def Tree.rebaseHashInputs {T : Type} (orig base : Tree T) (depth : Nat) :
    _root_.List (BinaryHashInputPair T) := by
  classical
  exact match orig, base with
  | .Node hash left right, .Node baseHash baseLeft baseRight =>
    if triomphe.arc.Arc.ptr_eq (.Node hash left right : Tree T) (.Node baseHash baseLeft baseRight) = ok false then
      let children := left.rebaseHashInputs baseLeft (depth - 1) ++
        right.rebaseHashInputs baseRight (depth - 1)
      if hash = Array.repeat 32#usize 0#u8 then children
      else (depth, left.elements ++ right.elements, baseLeft.elements ++ baseRight.elements) :: children
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
    simp [hclear.1, ihleft baseLeft (depth - 1) hclear.2.1,
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
    refine ⟨?_, ihleft baseLeft hclear.2.1, ihright baseRight hclear.2.2⟩
    intro hnonzero
    apply False.elim
    apply hnonzero
    simp [hclear.1, Array.repeat]

/-- Valid caches and collision soundness on the corresponding finite hash
inputs establish the operational shortcut law required by rebasing. Depths
are tracked explicitly; no shape, element, packing, or execution law is used. -/
theorem Tree.cachedHashesAgree_of_valid_caches {T : Type}
    (reference : CacheSubject T → CacheHash) (orig base : Tree T) (depth : Nat)
    (horig : orig.CachesOn (CacheValidFor reference) depth)
    (hbase : base.CachesOn (CacheValidFor reference) depth)
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
      have hchildren : BinaryHashCollisionSoundOn reference
          (left.rebaseHashInputs baseLeft (depth - 1) ++
            right.rebaseHashInputs baseRight (depth - 1)) := by
        apply hcollisions.mono
        intro pair hpair
        simp only [Tree.rebaseHashInputs, hpointer, ↓reduceIte]
        split <;> simp [hpair]
      refine ⟨?_, ihleft baseLeft (depth - 1) horig.2.1 hbase.2.1
          (hchildren.mono (fun pair hpair => List.mem_append_left _ hpair)),
        ihright baseRight (depth - 1) horig.2.2 hbase.2.2
          (hchildren.mono (fun pair hpair => List.mem_append_right _ hpair))⟩
      intro hnonzero hequal hlength
      have hnonzero' : hash ≠ Array.repeat 32#usize 0#u8 := by
        intro hzero
        apply hnonzero
        simp [hzero, Array.repeat]
      have hhash : hash = baseHash := Subtype.ext hequal
      have horigRef := horig.1.eq_reference_of_nonzero hnonzero'
      have hbaseRef := hbase.1.eq_reference_of_nonzero (by
        intro hzero
        exact hnonzero' (hhash.trans hzero))
      apply hcollisions (depth, left.elements ++ right.elements,
        baseLeft.elements ++ baseRight.elements)
      · simp [Tree.rebaseHashInputs, hpointer, hnonzero']
      · exact hlength
      · simpa only [← horigRef] using hnonzero'
      · exact horigRef.symm.trans (hhash.trans hbaseRef)

end tree
end milhouse
