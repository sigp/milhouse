import Tree.ProgressiveList.Decode.Finish
import Tree.ProgressiveList.Decode.State
import Tree.ProgressiveList.Construction.Caches
import Tree.Loop

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Every list finalized by the streaming decoder has cleared caches when
the input builder does. This includes partial lists finalized after an element
decode error, with no parser, finiteness, or element-codec laws. -/
theorem ProgressiveList.decode_ssz_items_loop_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (builder : ProgressiveTreeBuilder T)
    (hcache : builder.CachesCleared)
    {self : ProgressiveList T U} {decodeError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder =
      ok (core.result.Result.Ok self, decodeError)) :
    self.tree.CachesCleared := by
  let inv := fun (state : ssz_items.SszItems × ProgressiveTreeBuilder T) =>
    state.2.CachesCleared
  let post := fun (result : core.result.Result (ProgressiveList T U) error.Error ×
      Option ssz.decode.DecodeError) =>
    ∀ self, result.1 = core.result.Result.Ok self →
      self.tree.CachesCleared
  have hfinal : ∀ current, current.CachesCleared → ∀ error flow,
      Decode.finishBody ValueInst mapInst current error = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro current hcurrent error flow hfinish
    obtain ⟨status, rfl, houtcome⟩ := Decode.finishBody_outcome
      ValueInst mapInst current error hfinish
    intro self hself
    obtain ⟨hfinish, _⟩ := houtcome self hself
    exact ProgressiveTreeBuilder.finish_caches_cleared ValueInst current hcurrent hfinish
  have hbody : ∀ state, inv state → ∀ flow,
      ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst state.1 state.2 = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro ⟨cursor, current⟩ hinv flow hstep
    unfold ProgressiveList.decode_ssz_items_loop.body at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨entry, cursor1⟩, _, hstep⟩ := hstep
    dsimp! only at hstep
    cases entry with
    | none => exact hfinal current hinv none flow hstep
    | some entry =>
      rw [bind_eq_ok_iff] at hstep
      obtain ⟨decoded, _, hstep⟩ := hstep
      cases decoded with
      | Err error => exact hfinal current hinv (some error) flow hstep
      | Ok value =>
        rw [bind_eq_ok_iff] at hstep
        obtain ⟨⟨status, pushed⟩, hpush, hstep⟩ := hstep
        dsimp! only at hstep
        cases status with
        | Err error =>
          simp only [ok.injEq] at hstep
          subst flow
          simp [post]
        | Ok success =>
          cases success
          simp only [ok.injEq] at hstep
          subst flow
          exact ProgressiveTreeBuilder.push_preserves_cleared_caches ValueInst current value hinv hpush
  exact loop_success_invariant
    (fun state => ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst state.1 state.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (items, builder) hcache _ hdecode self rfl

/-- Streaming construction initializes cleared caches from a fresh builder. -/
theorem ProgressiveList.decode_ssz_items_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems)
    {self : ProgressiveList T U} {decodeError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items ValueInst mapInst items =
      ok (core.result.Result.Ok self, decodeError)) :
    self.tree.CachesCleared := by
  unfold ProgressiveList.decode_ssz_items at hdecode
  rw [bind_eq_ok_iff] at hdecode
  obtain ⟨status, hnew, hdecode⟩ := hdecode
  cases status with
  | Err e => simp at hdecode
  | Ok builder =>
    exact ProgressiveList.decode_ssz_items_loop_caches_cleared ValueInst mapInst items builder
      (ProgressiveTreeBuilder.new_caches_cleared ValueInst hnew) hdecode

/-- Every successful public SSZ decoder initializes all caches to zero.
Input validity, element decoding, packing, and map behavior are unrestricted. -/
theorem ProgressiveList.from_ssz_bytes_caches_cleared {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    self.tree.CachesCleared := by
  rcases ProgressiveList.from_ssz_bytes_success_source ValueInst mapInst bytes hdecode with
    hempty | ⟨items, hitems⟩
  · exact ProgressiveList.empty_caches_cleared ValueInst mapInst hempty
  · exact ProgressiveList.decode_ssz_items_caches_cleared ValueInst mapInst items hitems


theorem ProgressiveList.from_ssz_bytes_valid_caches {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (reference : CacheSubject T → CacheHash)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (.Ok self)) : self.tree.CachesOn (CacheValidFor reference) 0 :=
  (ProgressiveList.from_ssz_bytes_caches_cleared ValueInst mapInst bytes hdecode).cachesOn
    (CacheValidFor reference) (CacheValidFor.zero reference) 0

end milhouse.progressive_list
