import Tree.Invariants

namespace milhouse.tree

/-- A dense extension restricted to one subtree's global index window.
    Updates outside this window are immaterial to that subtree. -/
structure DenseUpdateWindow (hasUpdate : Nat → Prop)
    (start capacity oldLength newLength : Nat) : Prop where
  length_mono : oldLength ≤ newLength
  extension_complete : ∀ index, oldLength ≤ index → index < newLength →
    hasUpdate (start + index)
  updates_bounded : ∀ index, index < capacity → hasUpdate (start + index) →
    index < newLength

/-- Restrict a global dense update domain to a bounded subtree interval. -/
theorem DenseUpdateDomain.window {hasUpdate : Nat → Prop}
    {oldLength newLength : Nat} (h : DenseUpdateDomain oldLength newLength hasUpdate)
    (start capacity : Nat) :
    DenseUpdateWindow hasUpdate start capacity
      (min (oldLength - start) capacity) (min (newLength - start) capacity) := by
  refine ⟨by have := h.length_mono; omega, ?_, ?_⟩
  · intro index hlo hhi
    exact h.extension_complete (start + index) (by omega) (by omega)
  · intro index hcap hhas
    have := h.updates_bounded (start + index) hhas
    omega

/-- Split the update window at a binary node. Density of the old children
    gives the same left-first division of both the old and new lengths. -/
theorem DenseUpdateWindow.split {hasUpdate : Nat → Prop}
    {start capacity leftLength rightLength newLength : Nat}
    (h : DenseUpdateWindow hasUpdate start (capacity * 2)
      (leftLength + rightLength) newLength)
    (hleft : leftLength ≤ capacity)
    (hfull : 0 < rightLength → leftLength = capacity) :
    DenseUpdateWindow hasUpdate start capacity leftLength (min newLength capacity) ∧
      DenseUpdateWindow hasUpdate (start + capacity) capacity rightLength
        (newLength - capacity) := by
  have hmono := h.length_mono
  have hold : rightLength = 0 ∨ leftLength = capacity := by
    by_cases hr : 0 < rightLength
    · exact Or.inr (hfull hr)
    · exact Or.inl (by omega)
  constructor
  · refine ⟨by omega, ?_, ?_⟩
    · intro index hlo hhi
      apply h.extension_complete index
      · rcases hold with hr | hl <;> omega
      · omega
    · intro index hi hhas
      have := h.updates_bounded index (by omega) hhas
      omega
  · refine ⟨?_, ?_, ?_⟩
    · rcases hold with hr | hl <;> omega
    · intro index hlo hhi
      have := h.extension_complete (capacity + index) (by omega) (by omega)
      simpa only [Nat.add_assoc] using this
    · intro index hi hhas
      have hh : hasUpdate (start + (capacity + index)) := by
        simpa only [Nat.add_assoc] using hhas
      have := h.updates_bounded (capacity + index) (by omega) hh
      omega

/-- A window without updates retains its old dense length. -/
theorem DenseUpdateWindow.length_eq_of_empty {hasUpdate : Nat → Prop}
    {start capacity oldLength newLength : Nat}
    (h : DenseUpdateWindow hasUpdate start capacity oldLength newLength)
    (hcap : newLength ≤ capacity)
    (hempty : ¬ ∃ index, index < capacity ∧ hasUpdate (start + index)) :
    newLength = oldLength := by
  have hmono := h.length_mono
  by_contra hne
  exact hempty ⟨oldLength, by omega,
    h.extension_complete oldLength (Nat.le_refl _) (by omega)⟩

/-- A window containing an update has a positive new dense length. -/
theorem DenseUpdateWindow.length_pos_of_update {hasUpdate : Nat → Prop}
    {start capacity oldLength newLength : Nat}
    (h : DenseUpdateWindow hasUpdate start capacity oldLength newLength)
    (hhas : ∃ index, index < capacity ∧ hasUpdate (start + index)) :
    0 < newLength := by
  obtain ⟨index, hi, hhas⟩ := hhas
  have := h.updates_bounded index hi hhas
  omega

end milhouse.tree
