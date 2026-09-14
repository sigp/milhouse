import Tree.ProgressiveList.Length

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

private theorem metadata_length_zero_iff {backing count : Std.Usize} {largest : Option Std.Usize}
    (hvalue : count.val = largest.elim backing.val (fun last => max (last.val + 1) backing.val)) :
    count = 0#usize ↔ backing = 0#usize ∧ largest = none := by
  cases largest with
  | none =>
    simp only [Option.elim_none] at hvalue
    have heq : count = backing := by scalar_tac
    simp only [heq, and_true]
  | some last =>
    simp only [Option.elim_some] at hvalue
    have hnonzero : count ≠ 0#usize := by scalar_tac
    simp only [hnonzero, Option.some_ne_none, and_false]

/-- The emptiness observer succeeds when a present maximum has a
representable successor. Its exact answer is true precisely for zero backing
length and absent maximum metadata. The actual length call is derived here;
no sequence reads, representation, backing, or packing law is assumed. -/
theorem ProgressiveList.is_empty_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest)
    (hbound : ∀ last, largest = some last → last.val < Std.Usize.max) :
    ProgressiveList.is_empty ValueInst mapInst self =
      ok (decide (self.length = 0#usize ∧ largest = none)) := by
  obtain ⟨length, hlen, hvalue⟩ := ProgressiveList.len_total_spec
    ValueInst mapInst self largest hmax hbound
  rw [ProgressiveList.is_empty_spec ValueInst mapInst self length hlen]
  simp only [metadata_length_zero_iff hvalue]

/-- The successor check is necessary and sufficient for a returned emptiness
answer once the optional maximum is known. In particular, the comparison with
zero does not bypass an overflowing length calculation. -/
theorem ProgressiveList.is_empty_success_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (largest : Option Std.Usize)
    (hmax : mapInst.max_index self.updates = ok largest) :
    (∃ empty, ProgressiveList.is_empty ValueInst mapInst self = ok empty) ↔
      ∀ last, largest = some last → last.val < Std.Usize.max := by
  constructor
  · rintro ⟨empty, hempty⟩
    cases hlen : ProgressiveList.len ValueInst mapInst self with
    | fail e => simp [ProgressiveList.is_empty, hlen] at hempty
    | div => simp [ProgressiveList.is_empty, hlen] at hempty
    | ok length =>
      exact (ProgressiveList.len_success_iff ValueInst mapInst self largest hmax).mp ⟨length, hlen⟩
  · intro hbound
    exact ⟨_, ProgressiveList.is_empty_total_spec ValueInst mapInst self largest hmax hbound⟩

/-- Returning true is equivalent to zero backing length and an actual absent
map maximum, with no assumed metadata or length success. This concerns the
logical-length observer; the map's separate `is_empty` method is never used. -/
theorem ProgressiveList.is_empty_true_iff {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) :
    ProgressiveList.is_empty ValueInst mapInst self = ok true ↔
      self.length = 0#usize ∧ mapInst.max_index self.updates = ok none := by
  constructor
  · intro hempty
    cases hmax : mapInst.max_index self.updates with
    | fail e => simp [ProgressiveList.is_empty, ProgressiveList.len, utils.updated_length, hmax] at hempty
    | div => simp [ProgressiveList.is_empty, ProgressiveList.len, utils.updated_length, hmax] at hempty
    | ok largest =>
      have hbound := (ProgressiveList.is_empty_success_iff ValueInst mapInst self largest hmax).mp
        ⟨true, hempty⟩
      rw [ProgressiveList.is_empty_total_spec ValueInst mapInst self largest hmax hbound] at hempty
      have hzero : self.length = 0#usize ∧ largest = none := by
        simpa only [ok.injEq, decide_eq_true_eq] using hempty
      exact ⟨hzero.1, by simp only [hzero.2]⟩
  · rintro ⟨hzero, hmax⟩
    have hbound : ∀ last, (none : Option Std.Usize) = some last → last.val < Std.Usize.max := by
      intro last hlast
      cases hlast
    simpa only [hzero, and_true, decide_true] using
      ProgressiveList.is_empty_total_spec ValueInst mapInst self none hmax hbound

end milhouse.progressive_list
