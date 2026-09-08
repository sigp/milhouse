import Tree.Funs
import Tree.Formatting.Utf8

open Aeneas Aeneas.Std Result
open milhouse

namespace milhouse.error

/-- Default Rust Debug text for the public error enum. -/
def Error.debugText : Error → String
  | .OutOfBoundsUpdate index len => "OutOfBoundsUpdate { index: " ++ toString index.val ++ ", len: " ++ toString len.val ++ " }"
  | .OutOfBoundsIterFrom index len => "OutOfBoundsIterFrom { index: " ++ toString index.val ++ ", len: " ++ toString len.val ++ " }"
  | .ListFull len => "ListFull { len: " ++ toString len.val ++ " }"
  | .PackedLeafFull len => "PackedLeafFull { len: " ++ toString len.val ++ " }"
  | .LeafUpdateMissing index => "LeafUpdateMissing { index: " ++ toString index.val ++ " }"
  | .PackedLeafOutOfBounds index len => "PackedLeafOutOfBounds { sub_index: " ++ toString index.val ++ ", len: " ++ toString len.val ++ " }"
  | .NodeUpdatesMissing pos => "NodeUpdatesMissing { prefix: " ++ toString pos.val ++ " }"
  | .InvalidListUpdate => "InvalidListUpdate"
  | .InvalidVectorUpdate => "InvalidVectorUpdate"
  | .WrongVectorLength len expected => "WrongVectorLength { len: " ++ toString len.val ++ ", expected: " ++ toString expected.val ++ " }"
  | .PushNotSupported => "PushNotSupported"
  | .UpdateLeafError => "UpdateLeafError"
  | .UpdateLeavesError => "UpdateLeavesError"
  | .InvalidRebaseNode => "InvalidRebaseNode"
  | .InvalidRebaseLeaf => "InvalidRebaseLeaf"
  | .BuilderInvalidDepth depth => "BuilderInvalidDepth { depth: " ++ toString depth.val ++ " }"
  | .BuilderExpectedLeaf => "BuilderExpectedLeaf"
  | .BuilderStackEmptyMerge => "BuilderStackEmptyMerge"
  | .BuilderStackEmptyMergeLeft => "BuilderStackEmptyMergeLeft"
  | .BuilderStackEmptyMergeRight => "BuilderStackEmptyMergeRight"
  | .BuilderStackEmptyFinish => "BuilderStackEmptyFinish"
  | .BuilderStackEmptyFinishLeft => "BuilderStackEmptyFinishLeft"
  | .BuilderStackEmptyFinishRight => "BuilderStackEmptyFinishRight"
  | .BuilderStackEmptyFinalize => "BuilderStackEmptyFinalize"
  | .BuilderStackLeftover => "BuilderStackLeftover"
  | .BuilderFull => "BuilderFull"
  | .CowMissingEntry => "CowMissingEntry"
  | .LevelIterPendingUpdates => "LevelIterPendingUpdates"
  | .IntraRebaseZeroHash => "IntraRebaseZeroHash"
  | .IntraRebaseZeroDepth => "IntraRebaseZeroDepth"
  | .IntraRebaseRepeatVisit => "IntraRebaseRepeatVisit"

/-- The actual extracted derived formatter appends the exact default Debug
text, preserving its existing destination. No opaque Error formatter is used. -/
theorem Error.debug_fmt_spec (error : Error) (buffer : String) :
    Error.Insts.CoreFmtDebug.fmt error buffer =
      ok (core.result.Result.Ok (), buffer ++ error.debugText) := by
  have hlen (s : String) : s ++ ", " ++ "len" ++ ": " = s ++ ", len: " := by
    simp only [String.append_assoc]
    rfl
  have hexpected (s : String) : s ++ ", " ++ "expected" ++ ": " = s ++ ", expected: " := by
    simp only [String.append_assoc]
    rfl
  cases error <;>
    first | rfl | simp [Error.Insts.CoreFmtDebug.fmt, Error.debugText,
      milhouse_fmt.Formatter.write_str,
      milhouse_fmt.Formatter.debug_struct_field1_finish,
      milhouse_fmt.Formatter.debug_struct_field2_finish,
      milhouse_fmt.formatDyn, milhouse_fmt.DebugShared,
      milhouse_fmt.DebugUsize, milhouse_fmt.utf8_toStr, String.append_assoc] <;>
    simp only [← String.append_assoc, hlen, hexpected] <;> rfl

end milhouse.error
