import Tree.ProgressiveList.Decode.Contents
import Tree.Ssz.PayloadTrace
import Tree.Loop

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree milhouse.ssz_items

namespace milhouse.progressive_list

/-- A successful streaming result determines a finite trace of the actual
element calls and their individual payloads, including the retained stopping
error. No parser trace, builder invariant, or element-codec law is assumed. -/
theorem ProgressiveList.decode_ssz_items_loop_trace {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : SszItems) (builder : ProgressiveTreeBuilder T)
    {self : ProgressiveList T U} {reportedError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder =
      ok (core.result.Result.Ok self, reportedError)) :
    ∃ entries : _root_.List (T × _root_.List Std.U8),
      items.Decodes (SszItems.recordPayload ValueInst.sszdecodeDecodeInst.from_ssz_bytes)
        entries reportedError := by
  let decode := SszItems.recordPayload ValueInst.sszdecodeDecodeInst.from_ssz_bytes
  let inv := fun (state : SszItems × ProgressiveTreeBuilder T) =>
    ∀ entries flag, state.1.Decodes decode entries flag →
      ∃ whole, items.Decodes decode whole flag
  let post := fun (result : core.result.Result (ProgressiveList T U) error.Error ×
      Option ssz.decode.DecodeError) =>
    ∀ self, result.1 = core.result.Result.Ok self →
      ∃ entries, items.Decodes decode entries result.2
  have hfinal : ∀ cursor current, inv (cursor, current) → ∀ flag,
      cursor.Decodes decode [] flag → ∀ flow,
      Decode.finishBody ValueInst mapInst current flag = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro cursor current hinv flag htrace flow hfinish
    obtain ⟨status, rfl, _⟩ := Decode.finishBody_outcome
      ValueInst mapInst current flag hfinish
    intro self hself
    exact hinv [] flag htrace
  have hbody : ∀ state, inv state → ∀ flow,
      ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst state.1 state.2 = ok flow →
      match flow with
      | .cont next => inv next
      | .done result => post result := by
    intro ⟨cursor, current⟩ hinv flow hstep
    unfold ProgressiveList.decode_ssz_items_loop.body at hstep
    rw [bind_eq_ok_iff] at hstep
    obtain ⟨⟨entry, cursor1⟩, hnext, hstep⟩ := hstep
    dsimp! only at hstep
    cases entry with
    | none => exact hfinal cursor current hinv none (.exhausted hnext) flow hstep
    | some entry =>
      cases entry with
      | Err error =>
        simp only [bind_tc_ok] at hstep
        exact hfinal cursor current hinv (some error) (.boundary_error hnext) flow hstep
      | Ok bytes =>
        rw [bind_eq_ok_iff] at hstep
        obtain ⟨decoded, hdecoded, hstep⟩ := hstep
        cases decoded with
        | Err error =>
          exact hfinal cursor current hinv (some error)
            (.element_error hnext
              ((SszItems.recordPayload_error_iff _ _ _).mpr hdecoded)) flow hstep
        | Ok value =>
          rw [bind_eq_ok_iff] at hstep
          obtain ⟨⟨status, pushed⟩, _, hstep⟩ := hstep
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
            intro entries flag htail
            exact hinv ((value, bytes.val) :: entries) flag
              (.cons hnext ((SszItems.recordPayload_ok_iff _ _ _).mpr ⟨hdecoded, rfl⟩) htail)
  exact loop_success_invariant
    (fun state => ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst state.1 state.2)
    inv post (by
      intro state hinv flow hstep
      cases flow with
      | cont next => exact hbody state hinv (.cont next) hstep
      | done result => exact hbody state hinv (.done result) hstep)
    (items, builder) (by intro entries flag htrace; exact ⟨entries, htrace⟩)
    _ hdecode self rfl

/-- Successful streaming construction reflects the actual per-occurrence
payload trace and stores exactly its values and count with the actual default
map. This converse has no metadata, packing, parser, or codec-law premises. -/
theorem ProgressiveList.decode_ssz_items_trace {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : SszItems) {self : ProgressiveList T U}
    {reportedError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items ValueInst mapInst items =
      ok (core.result.Result.Ok self, reportedError)) :
    ∃ entries : _root_.List (T × _root_.List Std.U8),
      items.Decodes (SszItems.recordPayload ValueInst.sszdecodeDecodeInst.from_ssz_bytes)
        entries reportedError ∧
      self.tree.elements = entries.map Prod.fst ∧ self.length.val = entries.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  have htrace : ∃ entries : _root_.List (T × _root_.List Std.U8),
      items.Decodes (SszItems.recordPayload ValueInst.sszdecodeDecodeInst.from_ssz_bytes)
        entries reportedError := by
    unfold ProgressiveList.decode_ssz_items at hdecode
    rw [bind_eq_ok_iff] at hdecode
    obtain ⟨status, _, hdecode⟩ := hdecode
    cases status with
    | Err error => simp at hdecode
    | Ok builder =>
      exact ProgressiveList.decode_ssz_items_loop_trace ValueInst mapInst items builder hdecode
  obtain ⟨entries, htrace⟩ := htrace
  obtain ⟨helements, hlength, hdefault, _⟩ := ProgressiveList.decode_ssz_items_contents
    ValueInst mapInst items (entries.map Prod.fst) reportedError
    (htrace.forget_payload _ _ _ _) hdecode
  exact ⟨entries, htrace, helements, by simpa using hlength, hdefault⟩

end milhouse.progressive_list
