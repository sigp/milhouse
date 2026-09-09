import Tree.ProgressiveList.Push

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

/-- Observable representation of a finite sequence: length and every
    machine-indexed lookup agree with the sequence, including out-of-bounds
    reads. This is separate from the structural tree invariants needed to
    justify rebuilding and bulk updates. -/
def ProgressiveList.Represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) : Prop :=
  (∃ length, ProgressiveList.len ValueInst mapInst self = ok length ∧
    length.val = contents.length) ∧
  ∀ index, ProgressiveList.get ValueInst mapInst self index = ok contents[index.val]?

/-- Empty construction represents the empty sequence. All requirements on
    the generic default map are stated explicitly as empty-map laws. -/
theorem ProgressiveList.empty_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ i, mapInst.get updates i = ok none)
    (hmax : mapInst.max_index updates = ok none) :
    ∃ self, ProgressiveList.empty ValueInst mapInst = ok self ∧
      self.Represents ValueInst mapInst [] := by
  let self : ProgressiveList T U :=
    { tree := .ProgressiveZero, length := 0#usize, updates }
  refine ⟨self, ProgressiveList.empty_eq ValueInst mapInst updates hdefault,
    ⟨⟨0#usize, ProgressiveList.len_of_no_max_index ValueInst mapInst self hmax, rfl⟩,
      ?_⟩⟩
  intro i
  exact ProgressiveList.get_none_of_backing_bound ValueInst mapInst self i
    (hget i) (by simp [self])

/-- `Default::default` represents the empty sequence under the same map laws. -/
theorem ProgressiveList.default_represents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ i, mapInst.get updates i = ok none)
    (hmax : mapInst.max_index updates = ok none) :
    ∃ self, ProgressiveList.Insts.CoreDefaultDefault.default ValueInst mapInst = ok self ∧
      self.Represents ValueInst mapInst [] := by
  rw [ProgressiveList.default_eq_empty]
  exact ProgressiveList.empty_represents ValueInst mapInst updates hdefault hget hmax

/-- **Sequence-level append correctness.** If a list represents `contents`,
    a successful push represents `contents ++ [value]`, at the new length and
    every index. The map laws are restricted to the actual insertion at the
    old logical end. No structural assumptions on the backing tree are needed
    for this operation, which leaves that tree untouched. -/
theorem ProgressiveList.push_represents_append {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (self : ProgressiveList T U) (contents : _root_.List T) (value : T)
    (hrep : self.Represents ValueInst mapInst contents)
    (hinsert : ∀ index previous updates,
      ProgressiveList.len ValueInst mapInst self = ok index →
      mapInst.insert self.updates index value = ok (previous, updates) →
      mapInst.max_index updates = ok (some index) ∧
      ∀ query, self.AppendReadAgrees ValueInst mapInst updates index value query)
    {pushed : ProgressiveList T U}
    (hpush : ProgressiveList.push ValueInst mapInst self value =
      ok (core.result.Result.Ok (), pushed)) :
    pushed.Represents ValueInst mapInst (contents ++ [value]) := by
  obtain ⟨⟨index, hlen, hcontentlen⟩, hreads⟩ := hrep
  obtain ⟨length, hlength, hlengthval⟩ :=
    ProgressiveList.len_after_push ValueInst mapInst self value index hlen
      (fun previous updates hins => (hinsert index previous updates hlen hins).1) hpush
  refine ⟨⟨length, hlength, by simp [hlengthval, hcontentlen]⟩, ?_⟩
  intro query
  rw [ProgressiveList.get_after_push_at ValueInst mapInst self value index query hlen
    (fun previous updates hins => (hinsert index previous updates hlen hins).2 query) hpush]
  by_cases heq : query = index
  · subst query
    rw [if_pos rfl, hcontentlen, _root_.List.getElem?_concat_length]
  · rw [if_neg heq, hreads query]
    congr 1
    symm
    by_cases hlt : query.val < contents.length
    · exact _root_.List.getElem?_append_left hlt
    · have hne : query.val ≠ contents.length := by
        intro heqval
        have hsame : query = index := by scalar_tac
        exact heq hsame
      have hle : contents.length ≤ query.val := by omega
      rw [_root_.List.getElem?_append_right hle]
      have hleft : contents[query.val]? = none :=
        _root_.List.getElem?_eq_none_iff.mpr hle
      have hright : [value][query.val - contents.length]? = none :=
        _root_.List.getElem?_eq_none_iff.mpr (by simp; omega)
      rw [hleft, hright]

end milhouse.progressive_list
