import Tree.ProgressiveList.Contents
import Tree.Ssz.ReadOffset

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

theorem ProgressiveList.decode_is_fixed_len_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) :
    ProgressiveList.Insts.SszDecodeDecode.is_ssz_fixed_len ValueInst mapInst = ok false := rfl

theorem ProgressiveList.decode_fixed_len_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) :
    ProgressiveList.Insts.SszDecodeDecode.ssz_fixed_len ValueInst mapInst = ok 4#usize := rfl

/-- Empty input bypasses every element metadata/decoder call, even for
zero-sized element types. Only the actual empty constructor is evaluated. -/
theorem ProgressiveList.from_ssz_bytes_empty_eq {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (hbytes : bytes.val = []) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      (do let self ← ProgressiveList.empty ValueInst mapInst
          ok (core.result.Result.Ok self)) := by
  simp [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes,
    core.slice.Slice.is_empty, hbytes]

/-- Empty SSZ input represents the empty sequence and has no pending updates.
No packing or element-codec premises are needed. -/
theorem ProgressiveList.from_ssz_bytes_empty_spec {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (hbytes : bytes.val = []) (updates : U)
    (hdefault : mapInst.coredefaultDefaultInst.default = ok updates)
    (hget : ∀ index, mapInst.get updates index = ok none)
    (hmax : mapInst.max_index updates = ok none)
    (hempty : mapInst.is_empty updates = ok true) :
    ∃ self, ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Ok self) ∧ self.Represents ValueInst mapInst [] ∧
      ProgressiveList.has_pending_updates ValueInst mapInst self = ok false := by
  obtain ⟨self, hself, hrep⟩ := ProgressiveList.empty_represents
    ValueInst mapInst updates hdefault hget hmax
  refine ⟨self, ?_, hrep, ?_⟩
  · rw [ProgressiveList.from_ssz_bytes_empty_eq ValueInst mapInst bytes hbytes, hself]
    rfl
  · have heq := ProgressiveList.empty_eq ValueInst mapInst updates hdefault
    rw [hself] at heq
    cases heq
    exact ProgressiveList.has_pending_updates_spec ValueInst mapInst _ true hempty

/-- Nonempty fixed-format input with declared zero element width returns the
SSZ zero-length error before allocating a builder or calling the element decoder. -/
theorem ProgressiveList.from_ssz_bytes_zero_width {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (hnonempty : bytes.val ≠ [])
    (hfixed : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok true)
    (hwidth : ValueInst.sszdecodeDecodeInst.ssz_fixed_len = ok 0#usize) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err ssz.decode.DecodeError.ZeroLengthItem) := by
  simp [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes,
    core.slice.Slice.is_empty, hnonempty, hfixed, hwidth]

/-- A nonempty variable-format input shorter than its first offset returns
the exact prefix error, without element decoding or list construction. -/
theorem ProgressiveList.from_ssz_bytes_short_variable {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T)
    (bytes : Slice Std.U8) (hnonempty : bytes.val ≠ []) (hshort : bytes.val.length < 4)
    (hvariable : ValueInst.sszdecodeDecodeInst.is_ssz_fixed_len = ok false) :
    ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes ValueInst mapInst bytes =
      ok (core.result.Result.Err (ssz.decode.DecodeError.InvalidLengthPrefix bytes.len 4#usize)) := by
  simp [ProgressiveList.Insts.SszDecodeDecode.from_ssz_bytes,
    core.slice.Slice.is_empty, hnonempty, hvariable, ssz_items.SszItems.variable,
    _root_.ssz.decode.read_offset_short bytes hshort,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

end milhouse.progressive_list
