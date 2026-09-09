import Tree.ProgressiveList.Decode.Contents
import Tree.ProgressiveList.Decode.Backing
import Tree.ProgressiveTree.Builder.New
import Tree.ProgressiveTree.Builder.PushLength
import Tree.ProgressiveTree.Builder.FinishSuccess

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder milhouse.progressive_tree

namespace milhouse.progressive_list

private theorem decode_exit_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (builder : ProgressiveTreeBuilder T)
    {factor : Option Std.Usize} (hvalid : builder.Valid ValueInst factor)
    (error : Option ssz.decode.DecodeError) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hbody : ProgressiveList.decode_ssz_items_loop.body ValueInst mapInst items builder =
      Decode.finishBody ValueInst mapInst builder error) :
    ∃ self, ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder =
      ok (core.result.Result.Ok self, error) := by
  obtain ⟨tree, hfinish⟩ := ProgressiveTreeBuilder.finish_success ValueInst builder hvalid.1
  refine ⟨{ tree, length := builder.length, updates }, ?_⟩
  rw [ProgressiveList.decode_ssz_items_loop, loop]
  simp! only [hbody, Decode.finishBody, hfinish, triomphe.arc.Arc.new, hdefault, bind_tc_ok]

/-- The streaming decoder terminates, builds every value in its decoded
prefix, and retains its stopping error. The final sequence-capacity bound
supplies every rollover check; element/cursor behavior is specified by actual
calls in `Decodes`, and the actual default map is initialized at the exit. -/
theorem ProgressiveList.decode_ssz_items_loop_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (builder : ProgressiveTreeBuilder T)
    (values : _root_.List T) (error : Option ssz.decode.DecodeError)
    (hitems : items.Decodes ValueInst.sszdecodeDecodeInst.from_ssz_bytes values error)
    {factor : Option Std.Usize} (hvalid : builder.Valid ValueInst factor)
    (hfits : ProgressiveTree.LengthFits factor (builder.length.val + values.length))
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.decode_ssz_items_loop ValueInst mapInst items builder =
      ok (core.result.Result.Ok self, error) := by
  induction hitems generalizing builder with
  | exhausted hnext =>
    exact decode_exit_success ValueInst mapInst _ builder hvalid none updates hdefault
      (by simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, bind_tc_ok]; rfl)
  | boundary_error hnext =>
    exact decode_exit_success ValueInst mapInst _ builder hvalid _ updates hdefault
      (by simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, bind_tc_ok]; rfl)
  | element_error hnext hdecoded =>
    exact decode_exit_success ValueInst mapInst _ builder hvalid _ updates hdefault
      (by simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, hdecoded, bind_tc_ok]; rfl)
  | @cons items rest bytes value values error hnext hdecoded htail ih =>
    obtain ⟨pushed, hpush, hvalidPushed, _, hlength⟩ :=
      ProgressiveTreeBuilder.push_length_fits_spec ValueInst builder hvalid
        (hfits.mono (by simp only [_root_.List.length_cons]; omega)) value
    have hfitsPushed : ProgressiveTree.LengthFits factor (pushed.length.val + values.length) := by
      simpa only [hlength, _root_.List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hfits
    obtain ⟨self, hrest⟩ := ih pushed hvalidPushed hfitsPushed
    refine ⟨self, ?_⟩
    rw [ProgressiveList.decode_ssz_items_loop, loop]
    simp! only [ProgressiveList.decode_ssz_items_loop.body, hnext, hdecoded, hpush, bind_tc_ok]
    exact hrest

/-- Streaming construction succeeds for any decoded prefix whose occupied
layers fit. Initialization and all builder invariants are established by the
actual constructor; no intermediate-success assumptions are exposed. -/
theorem ProgressiveList.decode_ssz_items_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (values : _root_.List T)
    (error : Option ssz.decode.DecodeError)
    (hitems : items.Decodes ValueInst.sszdecodeDecodeInst.from_ssz_bytes values error)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.decode_ssz_items ValueInst mapInst items =
      ok (core.result.Result.Ok self, error) := by
  obtain ⟨builder, hnew, hvalid, _, hlength⟩ := ProgressiveTreeBuilder.new_spec ValueInst hlayout
  obtain ⟨self, hloop⟩ := ProgressiveList.decode_ssz_items_loop_success ValueInst mapInst
    items builder values error hitems hvalid (by simpa only [hlength, Nat.zero_add] using hfits)
    updates hdefault
  exact ⟨self, by simp only [ProgressiveList.decode_ssz_items, hnew, bind_tc_ok, hloop]⟩

/-- Total streaming decoding constructs exactly the decoded prefix with its
recorded length, the supplied default map, and valid backing. The same result
covers ordinary exhaustion and the first boundary or element decoding error. -/
theorem ProgressiveList.decode_ssz_items_total_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (items : ssz_items.SszItems) (values : _root_.List T)
    (error : Option ssz.decode.DecodeError)
    (hitems : items.Decodes ValueInst.sszdecodeDecodeInst.from_ssz_bytes values error)
    {factor : Option Std.Usize} {packingDepth : Std.Usize}
    (hlayout : tree.PackingLayout ValueInst factor packingDepth)
    (hfits : ProgressiveTree.LengthFits factor values.length)
    (updates : U) (hdefault : mapInst.coredefaultDefaultInst.default = ok updates) :
    ∃ self, ProgressiveList.decode_ssz_items ValueInst mapInst items =
      ok (core.result.Result.Ok self, error) ∧ self.tree.elements = values ∧
      self.length.val = values.length ∧ self.updates = updates ∧ self.BackingValid factor := by
  obtain ⟨self, hdecode⟩ := ProgressiveList.decode_ssz_items_success ValueInst mapInst items values error
    hitems hlayout hfits updates hdefault
  obtain ⟨helements, hlength, hmap, _⟩ := ProgressiveList.decode_ssz_items_contents
    ValueInst mapInst items values error hitems hdecode
  obtain ⟨hbacking, _⟩ := ProgressiveList.decode_ssz_items_backing ValueInst mapInst items hlayout hdecode
  rw [hdefault] at hmap
  exact ⟨self, hdecode, helements, hlength, (Result.ok.inj hmap).symm, hbacking⟩

end milhouse.progressive_list
