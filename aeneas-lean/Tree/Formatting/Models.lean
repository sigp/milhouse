import Aeneas

open Aeneas Aeneas.Std Result

/-! Observable formatting for the default-option error messages used by SSZ
decoding. Aeneas's built-in `Arguments := Unit` erases these messages. The
extraction script redirects the generated formatting calls to this local model.

Only the reached fragment is supported: default decimal usize debugging,
derived error structs, literal template pieces, and default placeholders.
Arguments retain deferred formatter calls, so constructing an argument does not
evaluate its formatter. Unsupported template opcodes fail explicitly. This is
not a model of arbitrary formatting flags or arbitrary user-provided sinks.
The template bytecode follows the pinned Rust core::fmt::write implementation.
-/

namespace milhouse_fmt

abbrev Error := core.fmt.Error
abbrev Formatter := String

structure Debug (T : Type u) where
  fmt : T → Formatter → Result (core.result.Result Unit Error × Formatter)

def utf8 (bytes : List Std.U8) : Result String :=
  match String.fromUTF8? ⟨(bytes.map fun b => UInt8.ofNat b.val).toArray⟩ with
  | some s => ok s
  | none => fail .panic

def Formatter.write_str (buffer : Formatter) (s : Str) :
    Result (core.result.Result Unit Error × Formatter) := do
  let s ← utf8 s.val
  ok (.Ok (), buffer ++ s)

def DebugUsize : Debug Std.Usize where
  fmt value buffer := ok (.Ok (), buffer ++ toString value.val)

def DebugShared {T : Type} (inst : Debug T) : Debug T := inst

def formatDyn (value : Dyn (fun T => Debug T)) (buffer : Formatter) :
    Result (core.result.Result Unit Error × Formatter) :=
  value.inst.fmt value.value buffer

def Formatter.debug_struct_field1_finish (buffer : Formatter) (typeName field : Str)
    (value : Dyn (fun T => Debug T)) :
    Result (core.result.Result Unit Error × Formatter) := do
  let typeName ← utf8 typeName.val
  let field ← utf8 field.val
  let (r, buffer) ← formatDyn value (buffer ++ typeName ++ " { " ++ field ++ ": ")
  match r with
  | .Err e => ok (.Err e, buffer)
  | .Ok () => ok (.Ok (), buffer ++ " }")

def Formatter.debug_struct_field2_finish (buffer : Formatter) (typeName field1 : Str)
    (value1 : Dyn (fun T => Debug T)) (field2 : Str)
    (value2 : Dyn (fun T => Debug T)) :
    Result (core.result.Result Unit Error × Formatter) := do
  let typeName ← utf8 typeName.val
  let field1 ← utf8 field1.val
  let (r, buffer) ← formatDyn value1 (buffer ++ typeName ++ " { " ++ field1 ++ ": ")
  match r with
  | .Err e => ok (.Err e, buffer)
  | .Ok () =>
    let field2 ← utf8 field2.val
    let (r, buffer) ← formatDyn value2 (buffer ++ ", " ++ field2 ++ ": ")
    match r with
    | .Err e => ok (.Err e, buffer)
    | .Ok () => ok (.Ok (), buffer ++ " }")

abbrev rt.Argument := Formatter → Result (core.result.Result Unit Error × Formatter)

def rt.Argument.new_debug {T : Type} (inst : Debug T) (value : T) :
    Result rt.Argument := ok (inst.fmt value)

structure Arguments where
  template : List Std.U8
  args : List rt.Argument

def Arguments.new {N M : Std.Usize} (template : Std.Array Std.U8 N)
    (args : Std.Array rt.Argument M) : Result Arguments :=
  ok ⟨template.val, args.val⟩

/-- Execute short literal pieces and default placeholders. Every instruction
consumes at least one template byte, so the initial byte length suffices. -/
def runTemplate (fuel : Nat) (template : List Std.U8)
    (args : List rt.Argument) (buffer : Formatter) : Result String :=
  match fuel with
  | 0 => fail .panic
  | fuel + 1 =>
    match template with
    | [] => fail .panic
    | opcode :: rest =>
      if opcode.val = 0 then ok buffer
      else if opcode.val < 128 then
        if opcode.val ≤ rest.length then do
          let literal ← utf8 (rest.take opcode.val)
          runTemplate fuel (rest.drop opcode.val) args (buffer ++ literal)
        else fail .panic
      else if opcode.val = 192 then
        match args with
        | [] => fail .panic
        | arg :: remaining => do
          let (r, output) ← arg buffer
          match r with
          | .Err _ => fail .panic
          | .Ok () => runTemplate fuel rest remaining output
      else fail .panic
termination_by structural fuel

end milhouse_fmt

def alloc.fmt.format (args : milhouse_fmt.Arguments) : Result String :=
  milhouse_fmt.runTemplate args.template.length args.template args.args ""
