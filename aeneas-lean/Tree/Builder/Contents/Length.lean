import Tree.Builder.Contents.Basic

open Aeneas Aeneas.Std Result
open milhouse milhouse.builder

namespace milhouse.tree

/-- The canonical forest's logical length counts precisely its materialized
values, independently of any successful finalization call. -/
theorem BuilderStack.elements_length {T : Type} {factor : Option Std.Usize}
    {base depth len : Nat} {stack : _root_.List (utils.MaybeArced (Tree T))}
    (hstack : BuilderStack factor base stack depth len) :
    (stackElements stack).length = len := by
  induction hstack with
  | empty => rfl
  | base entry len hdense hpositive =>
    simpa only [stackElements_singleton] using hdense.elements_length
  | full entry depth hbase hdense hpositive =>
    simpa only [stackElements_singleton] using hdense.elements_length
  | segment entry depth len hbase hdense hpositive hfinal =>
    simpa only [stackElements_singleton] using hdense.elements_length
  | left _ _ ih => exact ih
  | right entry depth len hdense htail hpositive hpartial ih =>
    simpa only [stackElements, _root_.List.flatMap_cons, _root_.List.length_append,
      hdense.elements_length] using congrArg (subtreeCapacity factor depth + ·) ih

/-- Builder validity already equates its counter with its complete value
sequence. No successful operation needs to be assumed to recover this fact. -/
theorem BuilderInvariant.elements_length {T : Type} {ValueInst : Value T} {self : Builder T}
    (hinvariant : BuilderInvariant ValueInst self) : self.elements.length = self.length.val :=
  (BuilderInvariant.stack_dense hinvariant).elements_length

end milhouse.tree
