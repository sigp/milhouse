import Tree.TypesExternal

open Aeneas Aeneas.Std Result

/-- The reached standard BTree vacant insertion (usize key, Global allocator)
stores the supplied value and lends it mutably. The backward continuation
retains the key and records the final value in the exclusive slot footprint.
Allocation failure is abstracted as in Aeneas's other collection models. -/
@[rust_fun
  "alloc::collections::btree::map::entry::{alloc::collections::btree::map::entry::VacantEntry<'a, @K, @V, @A>}::insert"]
def alloc.collections.btree.map.entry.VacantEntry.insert
    {K V A : Type} (_ : core.cmp.Ord K) (_ : core.clone.Clone A)
    (entry : alloc.collections.btree.map.entry.VacantEntry K V A) (value : V) :
    Result (V × (V → alloc.collections.btree.map.entry.VacantEntry K V A)) :=
  ok (value, fun replacement => { entry with value := some replacement })

/-- The local effect of vec_map 0.8.2's vacant insertion. Its `VecMap::insert`
first extends by `index - len + 1` if needed, then fills the vacant slot.
Checked subtraction/addition and the Aeneas vector-size bound are preserved.
The enclosing map continuation accounts for the newly occupied entry and
frames all other keys; capacity and allocation strategy are unobservable here. -/
@[rust_fun "vec_map::{vec_map::VacantEntry<'a, @V>}::insert"]
def vec_map.VacantEntry.insert {V : Type} (entry : vec_map.VacantEntry V) (value : V) :
    Result (V × (V → vec_map.VacantEntry V)) := do
  let backingLength ← if entry.backingLength ≤ entry.index then do
    let difference ← entry.index - entry.backingLength
    let added ← difference + 1#usize
    let size := entry.backingLength.val + added.val
    let grown : Result Std.Usize :=
      if h : size ≤ Std.Usize.max then ok (UScalar.ofNatCore size (by scalar_tac))
      else fail .maximumSizeExceeded
    grown
  else ok entry.backingLength
  ok (value, fun replacement => { entry with backingLength, value := some replacement })
