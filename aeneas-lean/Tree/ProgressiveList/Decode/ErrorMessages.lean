import Tree.Formatting.Error

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.progressive_list

theorem ProgressiveList.decode_fixed_build_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (error : error.Error) :
    DecodeProgressiveList.from_ssz_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleErrorDecodeError.call_once
      ValueInst mapInst () error = ok (ssz.decode.DecodeError.BytesInvalid
        ("Error building ssz ProgressiveList: " ++ error.debugText)) := by
  simp [DecodeProgressiveList.from_ssz_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleErrorDecodeError.call_once,
    milhouse_fmt.rt.Argument.new_debug,
    milhouse_fmt.Arguments.new, alloc.fmt.format, milhouse_fmt.runTemplate,
    core.hint.must_use, Array.make, milhouse.error.Error.debug_fmt_spec]
  rfl

theorem ProgressiveList.decode_variable_build_error {T U : Type}
    (ValueInst : Value T) (mapInst : update_map.UpdateMap U T) (error : error.Error) :
    DecodeProgressiveList.from_ssz_bytes.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorDecodeError.call_once
      ValueInst mapInst () error = ok (ssz.decode.DecodeError.BytesInvalid
        ("Error collecting into container: " ++ error.debugText)) := by
  simp [DecodeProgressiveList.from_ssz_bytes.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorDecodeError.call_once,
    milhouse_fmt.rt.Argument.new_debug,
    milhouse_fmt.Arguments.new, alloc.fmt.format, milhouse_fmt.runTemplate,
    core.hint.must_use, Array.make, milhouse.error.Error.debug_fmt_spec]
  rfl

end milhouse.progressive_list
