import Tree.ProgressiveList.Decode.Finish
import Tree.Ssz.DecodedItems

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

/-- Streaming decoding appends exactly the decoded prefix, preserves its
length, initializes the map once, and reports the first decoding error. The
same statement covers normal exhaustion and partial-builder finalization on
error. Contents need only counter agreement, without packing or clone laws. -/
theorem ProgressiveList.decode_ssz_items_loop_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (builder : ProgressiveTreeBuilder T)
    (values : _root_.List T) (error : Option ssz.decode.DecodeError)
    (hitems : items.Decodes ValueInst.sszdecodeDecodeInst.from_ssz_bytes values error)
    (hcount : builder.count.val = builder.current.elements.length)
    {self : ProgressiveList T U} {reportedError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder =
      ok (core.result.Result.Ok self, reportedError)) :
    self.tree.elements = builder.elements ++ values ∧
      self.length.val = builder.length.val + values.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates ∧ reportedError = error := by
  have hfinal : ∀ items builder flag, builder.count.val = builder.current.elements.length →
      ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst items builder =
        Decode.finishBody ValueInst mapInst builder flag →
      ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder =
        ok (core.result.Result.Ok self, reportedError) →
      self.tree.elements = builder.elements ∧ self.length = builder.length ∧
        mapInst.coredefaultDefaultInst.default = ok self.updates ∧ reportedError = flag := by
    intro items builder flag hcount hbody hloop
    obtain ⟨hfinish, hdefault, herr⟩ := Decode.finishBody_success ValueInst mapInst builder flag
      (Decode.loop_finishes ValueInst mapInst items builder flag hbody hloop)
    obtain ⟨helements, hlength⟩ := ProgressiveTreeBuilder.finish_elements
      ValueInst builder hcount hfinish
    exact ⟨helements, hlength, hdefault, herr⟩
  induction hitems generalizing builder with
  | exhausted hnext =>
    obtain ⟨helements, hlength, hdefault, herr⟩ := hfinal _ builder none hcount
      (by simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, bind_tc_ok]; rfl) hdecode
    simp [helements, hlength, hdefault, herr]
  | boundary_error hnext =>
    obtain ⟨helements, hlength, hdefault, herr⟩ := hfinal _ builder _ hcount
      (by simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, bind_tc_ok]; rfl) hdecode
    simp [helements, hlength, hdefault, herr]
  | element_error hnext hdecoded =>
    obtain ⟨helements, hlength, hdefault, herr⟩ := hfinal _ builder _ hcount
      (by simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, hdecoded, bind_tc_ok]; rfl) hdecode
    simp [helements, hlength, hdefault, herr]
  | @cons items rest bytes value values error hnext hdecoded htail ih =>
    rw [ProgressiveList.decode_ssz_items_loop, loop] at hdecode
    simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, hdecoded, bind_tc_ok] at hdecode
    cases hpush : ProgressiveTreeBuilder.push ValueInst builder value with
    | fail e => simp [hpush, Bind.bind, Std.bind] at hdecode
    | div => simp [hpush, Bind.bind, Std.bind] at hdecode
    | ok pair =>
      obtain ⟨status, pushed⟩ := pair
      cases status with
      | Err e => simp! [hpush, Bind.bind, Std.bind] at hdecode
      | Ok success =>
        cases success
        simp! only [hpush, bind_tc_ok] at hdecode
        obtain ⟨hpushed, hlength1, hcount1⟩ := ProgressiveTreeBuilder.push_contents
          ValueInst builder value hpush
        obtain ⟨helements, hlength, hdefault, herr⟩ := ih pushed (hcount1 hcount) hdecode
        refine ⟨?_, ?_, hdefault, herr⟩
        · simpa [hpushed, _root_.List.append_assoc] using helements
        · simpa [hlength1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength

/-- The streaming constructor materializes precisely the decoded prefix with
its exact length and default map. Initial counter agreement is established by
the actual builder constructor, so no builder or packing premise is exposed. -/
theorem ProgressiveList.decode_ssz_items_contents {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (values : _root_.List T)
    (error : Option ssz.decode.DecodeError)
    (hitems : items.Decodes ValueInst.sszdecodeDecodeInst.from_ssz_bytes values error)
    {self : ProgressiveList T U} {reportedError : Option ssz.decode.DecodeError}
    (hdecode : ProgressiveList.decode_ssz_items ValueInst mapInst items =
      ok (core.result.Result.Ok self, reportedError)) :
    self.tree.elements = values ∧ self.length.val = values.length ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates ∧ reportedError = error := by
  unfold ProgressiveList.decode_ssz_items at hdecode
  rw [bind_eq_ok_iff] at hdecode
  obtain ⟨status, hnew, hdecode⟩ := hdecode
  cases status with
  | Err e => simp at hdecode
  | Ok builder =>
    obtain ⟨hempty, hcounts⟩ := ProgressiveTreeBuilder.new_elements ValueInst hnew
    have hlength : builder.length.val = 0 := by simpa [hempty] using hcounts.2
    simpa [hempty, hlength] using ProgressiveList.decode_ssz_items_loop_contents
      ValueInst mapInst items builder values error hitems hcounts.1 hdecode

end milhouse.progressive_list
