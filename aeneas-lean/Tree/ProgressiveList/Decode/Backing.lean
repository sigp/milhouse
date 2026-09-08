import Tree.ProgressiveList.Decode.Finish
import Tree.ProgressiveList.Backing
import Tree.Loop

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Every list finalized by the streaming loop has valid backing layers and
the actual default map. This also covers a partial list finalized before a
decode error is returned. No parser, finiteness, or element-codec law is used. -/
theorem ProgressiveList.decode_ssz_items_loop_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (builder : ProgressiveTreeBuilder T)
    {factor : Option Std.Usize} (hvalid : builder.Valid ValueInst factor)
    {self : ProgressiveList T U} {decodeError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder =
      ok (core.result.Result.Ok self, decodeError)) :
    self.BackingValid factor ∧ mapInst.coredefaultDefaultInst.default = ok self.updates := by
  let inv := fun (state : ssz_items.SszItems × ProgressiveTreeBuilder T) =>
    state.2.Valid ValueInst factor
  let post := fun (result : core.result.Result (ProgressiveList T U) error.Error ×
      Option ssz.decode.DecodeError) =>
    ∀ self, result.1 = core.result.Result.Ok self →
      self.BackingValid factor ∧ mapInst.coredefaultDefaultInst.default = ok self.updates
  have hfinal : ∀ current, current.Valid ValueInst factor → ∀ error flow,
      Decode.finishBody ValueInst mapInst current error = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro current hcurrent error flow hfinish
    obtain ⟨status, rfl, houtcome⟩ := Decode.finishBody_outcome
      ValueInst mapInst current error hfinish
    intro self hself
    obtain ⟨hfinish, hdefault⟩ := houtcome self hself
    exact ⟨(ProgressiveTreeBuilder.finish_spec ValueInst current hcurrent hfinish).2.2, hdefault⟩
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
          exact ProgressiveTreeBuilder.push_preserves_valid ValueInst hinv value hpush
  exact loop_success_invariant
    (fun state => ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst state.1 state.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (items, builder) hvalid _ hdecode self rfl

/-- Successful streaming construction establishes backing validity from the
packing layout alone, independently of parsing, element laws, and map laws. -/
theorem ProgressiveList.decode_ssz_items_backing {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    {self : ProgressiveList T U} {decodeError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items ValueInst mapInst items =
      ok (core.result.Result.Ok self, decodeError)) :
    self.BackingValid factor ∧ mapInst.coredefaultDefaultInst.default = ok self.updates := by
  unfold ProgressiveList.decode_ssz_items at hdecode
  rw [bind_eq_ok_iff] at hdecode
  obtain ⟨status, hnew, hdecode⟩ := hdecode
  cases status with
  | Err e => simp at hdecode
  | Ok builder =>
    exact ProgressiveList.decode_ssz_items_loop_backing ValueInst mapInst items builder
      (ProgressiveTreeBuilder.new_valid ValueInst hlayout hnew) hdecode

end milhouse.progressive_list
