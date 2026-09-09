import Tree.ProgressiveList.Decode.Entry
import Tree.Builder.Contents.Basic

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.progressive_list

theorem ProgressiveList.empty_success_state {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    {self : ProgressiveList T U} (hempty : ProgressiveList.empty ValueInst mapInst = ok self) :
    self.tree = .ProgressiveZero ∧ self.length = 0#usize ∧
      mapInst.coredefaultDefaultInst.default = ok self.updates := by
  simp only [ProgressiveList.empty, progressive_tree.ProgressiveTree.empty,
    triomphe.arc.Arc.new, bind_tc_ok, bind_eq_ok_iff] at hempty
  obtain ⟨updates, hdefault, heq⟩ := hempty
  simp only [ok.injEq] at heq
  cases heq
  exact ⟨rfl, rfl, hdefault⟩

private theorem map_err_success {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (value : core.result.Result T E) (f : O)
    {result : T} (hmap : core.result.Result.map_err inst value f = ok (.Ok result)) :
    value = .Ok result := by
  cases value with
  | Ok x => simpa [core.result.Result.map_err] using hmap
  | Err e => simp [core.result.Result.map_err, bind_eq_ok_iff] at hmap

/-- A successful nonempty fixed-format public decode comes from the actual
fixed cursor and builder, and has no stored decode error. Formatting behavior
is irrelevant to this implication: map_err can never turn an error into a list. -/
theorem ProgressiveList.from_ssz_bytes_fixed_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (width : Std.Usize) (hnonempty : bytes.val ≠ [])
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width)
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    ProgressiveList.decode_ssz_items ValueInst mapInst (.Fixed bytes width) =
      ok (core.result.Result.Ok self, none) := by
  have hempty : core.slice.Slice.is_empty bytes = ok false := by
    simp [core.slice.Slice.is_empty, hnonempty]
  simp! only [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes,
    hempty, hfixed, hwidth, bind_tc_ok, Bool.false_eq_true,
    ↓reduceIte] at hdecode
  split at hdecode
  · simp at hdecode
  · rw [bind_eq_ok_iff] at hdecode
    obtain ⟨⟨built, error⟩, hbuild, hdecode⟩ := hdecode
    dsimp! only at hdecode
    rw [bind_eq_ok_iff] at hdecode
    obtain ⟨mapped, hmap, hdecode⟩ := hdecode
    cases error with
    | some error => simp at hdecode
    | none =>
      simp only [ok.injEq] at hdecode
      subst mapped
      have hb := map_err_success _ _ _ hmap
      rw [hb] at hbuild
      exact hbuild

/-- A successful nonempty variable-format decode comes from the initialized
cursor and a streaming construction with no retained decode error. -/
theorem ProgressiveList.from_ssz_bytes_variable_success {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (items : ssz_items.SszItems) (hnonempty : bytes.val ≠ [])
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false)
    (hitems : ssz_items.SszItems.variable bytes = ok (core.result.Result.Ok items))
    {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    ProgressiveList.decode_ssz_items ValueInst mapInst items =
      ok (core.result.Result.Ok self, none) := by
  have hempty : core.slice.Slice.is_empty bytes = ok false := by
    simp [core.slice.Slice.is_empty, hnonempty]
  simp! only [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes, hempty,
    hvariable, hitems, bind_tc_ok, Bool.false_eq_true, ↓reduceIte,
    core.result.Result.Insts.CoreOpsTry.branch] at hdecode
  rw [bind_eq_ok_iff] at hdecode
  obtain ⟨⟨built, error⟩, hbuild, hdecode⟩ := hdecode
  dsimp! only at hdecode
  cases error with
  | some error => simp at hdecode
  | none =>
    have hb := map_err_success _ _ _ hdecode
    simpa only [hb] using hbuild

/-- Successful public decoding identifies the actual input branch and cursor
initialization. Nonempty fixed input has positive declared width; variable
input passes its actual offset initialization. No metadata, parser validity,
packing, or element-codec law is assumed. -/
theorem ProgressiveList.from_ssz_bytes_success_input {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    (bytes.val = [] ∧ ProgressiveList.empty ValueInst mapInst = ok self) ∨
      (bytes.val ≠ [] ∧
        ((∃ width, ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true ∧
          ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok width ∧ width ≠ 0#usize ∧
          ProgressiveList.decode_ssz_items ValueInst mapInst (.Fixed bytes width) =
            ok (core.result.Result.Ok self, none)) ∨
        (ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false ∧
          ∃ items, ssz_items.SszItems.variable bytes = ok (core.result.Result.Ok items) ∧
            ProgressiveList.decode_ssz_items ValueInst mapInst items =
              ok (core.result.Result.Ok self, none)))) := by
  unfold ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes at hdecode
  rw [bind_eq_ok_iff] at hdecode
  obtain ⟨empty, hempty, hdecode⟩ := hdecode
  cases empty with
  | true =>
    simp only [if_true] at hdecode
    rw [bind_eq_ok_iff] at hdecode
    obtain ⟨result, hresult, hdecode⟩ := hdecode
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hdecode
    cases hdecode
    exact .inl ⟨by simpa [core.slice.Slice.is_empty] using hempty, hresult⟩
  | false =>
    refine .inr ⟨by simpa [core.slice.Slice.is_empty] using hempty, ?_⟩
    simp only [Bool.false_eq_true, if_false] at hdecode
    rw [bind_eq_ok_iff] at hdecode
    obtain ⟨fixed, hfixed, hdecode⟩ := hdecode
    cases fixed with
    | true =>
      simp only [if_true] at hdecode
      rw [bind_eq_ok_iff] at hdecode
      obtain ⟨width, hwidth, hdecode⟩ := hdecode
      split at hdecode
      · simp at hdecode
      · rename_i hnonzero
        rw [bind_eq_ok_iff] at hdecode
        obtain ⟨⟨built, error⟩, hbuild, hdecode⟩ := hdecode
        dsimp! only at hdecode
        rw [bind_eq_ok_iff] at hdecode
        obtain ⟨mapped, hmap, hdecode⟩ := hdecode
        cases error with
        | some error => simp at hdecode
        | none =>
          simp only [ok.injEq] at hdecode
          subst mapped
          have hb := map_err_success _ _ _ hmap
          exact .inl ⟨width, hfixed, hwidth, hnonzero, by simpa only [hb] using hbuild⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at hdecode
      rw [bind_eq_ok_iff] at hdecode
      obtain ⟨status, hitems, hdecode⟩ := hdecode
      cases status with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hdecode
      | Ok items =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hdecode
        rw [bind_eq_ok_iff] at hdecode
        obtain ⟨⟨built, error⟩, hbuild, hdecode⟩ := hdecode
        dsimp! only at hdecode
        cases error with
        | some error => simp at hdecode
        | none =>
          have hb := map_err_success _ _ _ hdecode
          exact .inr ⟨hfixed, items, hitems, by simpa only [hb] using hbuild⟩

/-- Every successful public decode is either the actual empty constructor or
a completed streaming construction with no decode error. This is the state
projection of the stronger input/cursor characterization. -/
theorem ProgressiveList.from_ssz_bytes_success_source {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) {self : ProgressiveList T U}
    (hdecode : ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self)) :
    ProgressiveList.empty ValueInst mapInst = ok self ∨
      ∃ items, ProgressiveList.decode_ssz_items ValueInst mapInst items =
        ok (core.result.Result.Ok self, none) := by
  rcases ProgressiveList.from_ssz_bytes_success_input ValueInst mapInst bytes hdecode with
    ⟨_, hempty⟩ | ⟨_, hsource⟩
  · exact .inl hempty
  · rcases hsource with ⟨width, _, _, _, hbuild⟩ | ⟨_, items, _, hbuild⟩
    · exact .inr ⟨.Fixed bytes width, hbuild⟩
    · exact .inr ⟨items, hbuild⟩

end milhouse.progressive_list
