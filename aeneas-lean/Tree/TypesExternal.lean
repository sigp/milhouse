-- [milhouse]: external types.
-- Hand-written models for the external (opaque) types.
--
-- The guiding principle: Aeneas's functionalization has already erased sharing
-- and aliasing, so pointer-like containers (`Arc`, `RwLock`) are modelled as
-- plain values. These are trusted *definitions* rather than axioms: a
-- definition cannot introduce logical inconsistency, and it lets proofs
-- compute. The trusted claim for each is stated in its docstring.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-- The pinned arbitrary 1.4.1 `Unstructured` stores exactly one remaining
borrowed byte slice. Functionalization makes that slice the complete state. -/
@[reducible, rust_type "arbitrary::unstructured::Unstructured"]
def arbitrary.unstructured.Unstructured : Type := Slice Std.U8

/-- The pinned arbitrary recursion-limit error is an empty Rust struct. -/
@[reducible, rust_type "arbitrary::MaxRecursionReached"]
def arbitrary.MaxRecursionReached : Type := Unit

/-- [std::collections::hash::map::HashMap]
    Modelled as an association list; the hasher state `S` and allocator `A` are
    semantically inert (see the hashing models in `FunsExternal.lean`). -/
@[reducible, rust_type "std::collections::hash::map::HashMap"]
def std.collections.hash.map.HashMap (K : Type) (V : Type) (S : Type) (A :
  Type) : Type := List (K × V)

/-- [std::hash::random::RandomState]
    Hashing is semantically inert in this development (the `HashMap` model
    compares keys with `Eq`, never hashes), so hasher state carries no
    information. -/
@[reducible, rust_type "std::hash::random::RandomState"]
def std.hash.random.RandomState : Type := Unit

/-- [std::hash::random::DefaultHasher] -/
@[reducible, rust_type "std::hash::random::DefaultHasher"]
def std.hash.random.DefaultHasher : Type := Unit

/-- The local footprint of an exclusively borrowed map entry. `none` records
    a vacant slot; the insertion continuation returns its final stored value.
    The enclosing map and its other keys are restored by the map continuation. -/
structure milhouse_models.BTreeEntrySlot (K V : Type) where
  key : K
  value : Option V

/-- Vector-map entry footprint. The original backing length determines the
    checked growth arithmetic in vec_map 0.8.2; it is not the occupied count. -/
structure milhouse_models.VecEntrySlot (V : Type) where
  index : Std.Usize
  backingLength : Std.Usize
  value : Option V

/-- [alloc::collections::btree::map::entry::VacantEntry]
    The reached BTreeCow uses usize keys and the Global allocator. -/
@[reducible, rust_type "alloc::collections::btree::map::entry::VacantEntry"
  (mutRegions := #[0])]
def alloc.collections.btree.map.entry.VacantEntry (K : Type) (V : Type) (A :
  Type) : Type := milhouse_models.BTreeEntrySlot K V

/-- [alloc::collections::btree::map::BTreeMap]
    Modelled as an association list, like `HashMap`. -/
@[reducible, rust_type "alloc::collections::btree::map::BTreeMap"]
def alloc.collections.btree.map.BTreeMap (K : Type) (V : Type) (A : Type) :
  Type := List (K × V)

/-- [lock_api::GuardNoSend] (marker type) -/
@[reducible, rust_type "lock_api::GuardNoSend"]
def lock_api.GuardNoSend : Type := Unit

/-- [lock_api::rwlock::RwLock]
    Modelled as the protected value itself. This is sound for the extracted
    subset because Aeneas only supports sequential code and no reachable
    function writes through a shared reference (`Tree::tree_hash`, which
    populates the hash caches through `&self`, is excluded from extraction).
    Revisit this model if interior mutability comes back into scope. -/
@[reducible, rust_type "lock_api::rwlock::RwLock"]
def lock_api.rwlock.RwLock (R : Type) (T : Type) : Type := T

/-- [lock_api::rwlock::RwLockReadGuard]
    A read guard is just the value it gives access to. -/
@[reducible, rust_type "lock_api::rwlock::RwLockReadGuard"]
def lock_api.rwlock.RwLockReadGuard (R : Type) (T : Type)
  (Clause0_GuardMarker : Type) : Type := T

/-- [parking_lot::raw_rwlock::RawRwLock]
    Lock state is invisible in a sequential model. -/
@[reducible, rust_type "parking_lot::raw_rwlock::RawRwLock"]
def parking_lot.raw_rwlock.RawRwLock : Type := Unit

/-- [core::mem::maybe_uninit::MaybeUninit]
    Initialization state is internal to `SmallVec`; translated code only
    observes initialized elements. -/
@[reducible, rust_type "core::mem::maybe_uninit::MaybeUninit"]
def core.mem.maybe_uninit.MaybeUninit (T : Type) : Type := T

/-- [smallvec::SmallVec]
    The inline-capacity optimization is invisible; a `SmallVec` is its
    elements. -/
@[reducible, rust_type "smallvec::SmallVec"]
def smallvec.SmallVec (A : Type) (Clause0_Item : Type) : Type :=
  List Clause0_Item

/-- The pinned SSZ encoder's complete state. The borrowed output buffer is
    carried as a value; external-function continuations restore its owner. -/
@[rust_type "ssz::encode::SszEncoder"]
structure ssz.encode.SszEncoder where
  offset : Std.Usize
  buf : alloc.vec.Vec Std.U8
  variable_bytes : alloc.vec.Vec Std.U8

/-- [triomphe::arc::Arc]
    Modelled as the pointed-to value: after functionalization, sharing is
    invisible and `Arc`'s safe API behaves exactly like a value of `T`
    (see `new`/`clone`/`deref` in `FunsExternal.lean`). The one operation this
    model cannot capture is `ptr_eq`, which is kept opaque with a
    characterizing axiom. -/
@[reducible, rust_type "triomphe::arc::Arc"]
def triomphe.arc.Arc (T : Type) : Type := T

/-- [vec_map::VacantEntry] Local entry state returned to the enclosing map. -/
@[reducible, rust_type "vec_map::VacantEntry" (mutRegions := #[0])]
def vec_map.VacantEntry (V : Type) : Type := milhouse_models.VecEntrySlot V
