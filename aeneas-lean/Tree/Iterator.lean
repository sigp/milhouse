import Aeneas

open Aeneas Aeneas.Std Result

namespace milhouse

/-- The values returned by successive successful `next` calls, up to the first
    `none`. No fused-iterator law or behavior after that first `none` is assumed. -/
inductive IteratorYields {I T : Type} (next : I → Result (Option T × I)) :
    I → _root_.List T → Prop where
  | nil {state rest : I} (hnext : next state = ok (none, rest)) :
      IteratorYields next state []
  | cons {state rest : I} {value : T} {values : _root_.List T}
      (hnext : next state = ok (some value, rest))
      (htail : IteratorYields next rest values) :
      IteratorYields next state (value :: values)

/-- Enumeration ending in a state whose `next` returns unchanged `none`.
    This stronger relation supports consumers that keep calling an exhausted
    iterator while processing a longer sequence from another source. -/
inductive IteratorDrains {I T : Type} (next : I → Result (Option T × I)) :
    I → _root_.List T → Prop where
  | nil {state : I} (hnext : next state = ok (none, state)) :
      IteratorDrains next state []
  | cons {state rest : I} {value : T} {values : _root_.List T}
      (hnext : next state = ok (some value, rest))
      (htail : IteratorDrains next rest values) :
      IteratorDrains next state (value :: values)

theorem IteratorDrains.yields {I T : Type} {next : I → Result (Option T × I)}
    {state : I} {values : _root_.List T} (h : IteratorDrains next state values) :
    IteratorYields next state values := by
  induction h with
  | nil hnext => exact .nil hnext
  | cons hnext _ ih => exact .cons hnext ih

/-- Successful conversion to an iterator whose next calls yield the input sequence. -/
def IntoIteratorYields {Input I T : Type}
    (iterInst : core.iter.traits.collect.IntoIterator Input T I)
    (input : Input) (values : _root_.List T) : Prop :=
  ∃ iter, iterInst.into_iter input = ok iter ∧ IteratorYields iterInst.iteratorInst.next iter values

theorem vec_iterator_yields {T : Type} (iter : alloc.vec.into_iter.IntoIter T) :
    IteratorYields (core.iter.traits.iterator.IteratorVecIntoIter T).next iter iter.val := by
  obtain ⟨values, hbound⟩ := iter
  induction values with
  | nil => exact .nil rfl
  | cons value values ih =>
    have htail : values.length ≤ Std.Usize.max := by simp only [_root_.List.length_cons] at hbound; omega
    exact .cons (rest := ⟨values, htail⟩) rfl (ih htail)

theorem vec_into_iterator_yields {T : Type} (values : alloc.vec.Vec T) :
    IntoIteratorYields (core.iter.traits.collect.IntoIteratorVec T) values values.val :=
  ⟨values, rfl, vec_iterator_yields values⟩

end milhouse
