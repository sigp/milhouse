-- [milhouse]: external functions.
-- Hand-written models for the external (opaque) functions.
--
-- Almost everything here is a *definition* (trusted model, cannot introduce
-- inconsistency) rather than an axiom. The only axioms are:
--   * `triomphe.arc.Arc.ptr_eq_spec`: pointer identity is invisible after
--     functionalization, so `ptr_eq` is opaque, characterized by the one
--     property the code relies on (`true` implies value equality).
--   * `core.mem.size_of.usize_spec`: `size_of` cannot be defined uniformly in
--     its type argument, so it is opaque with a spec at the one instantiation
--     the code uses (`usize`).
-- Hashing (`Hasher`/`Hash`/`BuildHasher`) is modelled as semantically inert:
-- hasher state is `Unit` and the `HashMap` model compares keys with `Eq`.
-- This is faithful because hashing only affects performance in Rust, never
-- observable behaviour (for law-abiding `Hash`/`Eq` impls).
import Aeneas
import Tree.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open milhouse

/-! ## Auxiliary definitions -/

namespace TreeAux

/-- Number of trailing zero bits of `n`, with recursion fuel `fuel`
    (`fuel = w` suffices for `n < 2^w`, `n ≠ 0`). -/
def natTrailingZeros (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if n % 2 = 0 then 1 + natTrailingZeros fuel (n / 2) else 0

/-- `BitVec.trailingZeros`, matching Rust's `trailing_zeros` (returns the
    bit-width on zero). -/
def bvTrailingZeros {w : Nat} (x : BitVec w) : Nat :=
  if x = 0 then w else natTrailingZeros w x.toNat

#assert bvTrailingZeros (0#16) = 16
#assert bvTrailingZeros (1#16) = 0
#assert bvTrailingZeros (8#16) = 3
#assert bvTrailingZeros (6#16) = 1

/-- Monadic association-list lookup, keyed through a monadic `borrow`/`eq`
    (used by the `HashMap`/`BTreeMap` models). -/
def lookup {K V Q : Type} (borrow : K → Result Q) (eq : Q → Q → Result Bool)
    (l : List (K × V)) (q : Q) : Result (Option V) :=
  match l with
  | [] => ok none
  | (k, v) :: rest => do
    let qk ← borrow k
    let b ← eq qk q
    if b then ok (some v) else lookup borrow eq rest q

/-- Monadic association-list insert; returns the previous value, keeps the
    original key (matching Rust's `HashMap::insert`). -/
def insert {K V : Type} (eq : K → K → Result Bool) (l : List (K × V)) (k : K)
    (v : V) : Result ((Option V) × List (K × V)) :=
  match l with
  | [] => ok (none, [(k, v)])
  | (k', v') :: rest => do
    let b ← eq k' k
    if b then ok (some v', (k', v) :: rest)
    else do
      let (old, rest') ← insert eq rest k v
      ok (old, (k', v') :: rest')

end TreeAux

/-! ## core -/

/-- [core::borrow::{impl core::borrow::Borrow<T> for T}::borrow]:
    The blanket impl: borrowing a value is the identity. -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T := ok

/-- [core::hash::impls::{impl core::hash::Hash for usize}::hash]:
    Hashing is semantically inert in this development (see header). -/
@[rust_fun "core::hash::impls::{core::hash::Hash<usize>}::hash"]
def Usize.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.Usize → H → Result H :=
  fun _ h => ok h

/-- [core::hash::impls::{impl core::hash::Hash for (T, B)}::hash]:
    Delegates to the component `Hash` impls. -/
@[rust_fun "core::hash::impls::{core::hash::Hash<(@T, @B)>}::hash"]
def Pair.Insts.CoreHashHash.hash
  {T : Type} {B : Type} {S : Type} (HashInst : core.hash.Hash T) (HashInst1 :
  core.hash.Hash B) (HasherInst : core.hash.Hasher S) :
  (T × B) → S → Result S :=
  fun p h => do
    let h1 ← HashInst.hash HasherInst p.1 h
    HashInst1.hash HasherInst p.2 h1

/-- [core::mem::size_of]:
    Cannot be defined uniformly in `T`; kept opaque with a spec at the one
    instantiation used (`usize`, in `utils::int_log`). -/
@[rust_fun "core::mem::size_of"]
opaque core.mem.size_of (T : Type) : Result Std.Usize

/-- Trusted spec for `size_of::<usize>()`: `usize` is `numBits / 8` bytes. -/
axiom core.mem.size_of.usize_spec :
  core.mem.size_of Std.Usize = ok ⟨ BitVec.ofNat _ (Usize.numBits / 8) ⟩

/-- [core::num::{usize}::trailing_zeros]: -/
@[rust_fun "core::num::{usize}::trailing_zeros"]
def core.num.Usize.trailing_zeros (x : Std.Usize) : Result Std.U32 :=
  ok ⟨ BitVec.ofNat _ (TreeAux.bvTrailingZeros x.bv) ⟩

/-- [core::num::{usize}::checked_next_power_of_two]:
    `Nat.nextPowerOfTwo` matches Rust's semantics (including `0 → 1`);
    `none` on overflow. -/
@[rust_fun "core::num::{usize}::checked_next_power_of_two"]
def core.num.Usize.checked_next_power_of_two (x : Std.Usize) :
    Result (Option Std.Usize) :=
  let p := Nat.nextPowerOfTwo x.val
  if p < Usize.size then ok (some ⟨ BitVec.ofNat _ p ⟩) else ok none

/-! ## core::option -/

/-- [core::option::{core::option::Option<T>}::is_none_or]: -/
@[rust_fun "core::option::{core::option::Option<@T>}::is_none_or"]
def core.option.Option.is_none_or
  {T : Type} {T1 : Type} (opsfunctionFnOnceT1TupleTBoolInst :
  core.ops.function.FnOnce T1 T Bool) :
  Option T → T1 → Result Bool :=
  fun o f =>
    match o with
    | none => ok true
    | some x => opsfunctionFnOnceT1TupleTBoolInst.call_once f x

/-- [core::option::{core::option::Option<T>}::unwrap_or_default]: -/
@[rust_fun "core::option::{core::option::Option<@T>}::unwrap_or_default"]
def core.option.Option.unwrap_or_default
  {T : Type} (defaultDefaultInst : core.default.Default T) :
  Option T → Result T :=
  fun o =>
    match o with
    | some x => ok x
    | none => defaultDefaultInst.default

/-- [core::option::{core::option::Option<T>}::map]: -/
@[rust_fun "core::option::{core::option::Option<@T>}::map"]
def core.option.Option.map
  {T : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) :
  Option T → F → Result (Option U) :=
  fun o f =>
    match o with
    | none => ok none
    | some x => do
      let y ← opsfunctionFnOnceFTupleTUInst.call_once f x
      ok (some y)

/-- [core::option::{core::option::Option<T>}::ok_or]: -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} : Option T → E → Result (core.result.Result T E) :=
  fun o e =>
    match o with
    | some x => ok (.Ok x)
    | none => ok (.Err e)

/-- [core::option::{core::option::Option<(T, U)>}::unzip]: -/
@[rust_fun "core::option::{core::option::Option<(@T, @U)>}::unzip"]
def core.option.OptionPair.unzip
  {T : Type} {U : Type} : Option (T × U) → Result ((Option T) × (Option U)) :=
  fun o =>
    match o with
    | some (a, b) => ok (some a, some b)
    | none => ok (none, none)

/-- [core::option::{core::option::Option<&'_0 T>}::copied]:
    Copying out of a shared reference is the identity in the pure model. -/
@[rust_fun "core::option::{core::option::Option<&'0 @T>}::copied"]
def core.option.OptionShared0T.copied
  {T : Type} (markerCopyInst : core.marker.Copy T) :
  Option T → Result (Option T) := ok

/-- [core::option::{core::option::Option<&'_0 T>}::cloned]:
    Delegates to the element's `Clone`. -/
@[rust_fun "core::option::{core::option::Option<&'0 @T>}::cloned"]
def core.option.OptionShared0T.cloned
  {T : Type} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T) :=
  fun o =>
    match o with
    | none => ok none
    | some x => do
      let y ← cloneCloneInst.clone x
      ok (some y)

/-- [core::option::{impl core::ops::try_trait::Try for core::option::Option<T>}::branch]: -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option
    core.convert.Infallible) T) :=
  fun o =>
    match o with
    | some x => ok (.Continue x)
    | none => ok (.Break none)

/-- [core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<core::convert::Infallible>> for core::option::Option<T>}::from_residual]:
    The residual of an `Option` is always `None` (`Infallible` is empty). -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  (T : Type) : Option core.convert.Infallible → Result (Option T) :=
  fun _ => ok none

/-! ## core::tuple -/

/-- [core::tuple::{impl core::cmp::PartialEq<(U, T)> for (U, T)}::eq]: -/
@[rust_fun "core::tuple::{core::cmp::PartialEq<(@U, @T), (@U, @T)>}::eq"]
def Pair.Insts.CoreCmpPartialEqPair.eq
  {U : Type} {T : Type} (cmpPartialEqInst : core.cmp.PartialEq U U)
  (cmpPartialEqInst1 : core.cmp.PartialEq T T) :
  (U × T) → (U × T) → Result Bool :=
  fun p q => do
    let b1 ← cmpPartialEqInst.eq p.1 q.1
    if b1 then cmpPartialEqInst1.eq p.2 q.2 else ok false

/-- [core::tuple::{impl core::cmp::PartialEq<(U, T)> for (U, T)}::ne]: -/
@[rust_fun "core::tuple::{core::cmp::PartialEq<(@U, @T), (@U, @T)>}::ne"]
def Pair.Insts.CoreCmpPartialEqPair.ne
  {U : Type} {T : Type} (cmpPartialEqInst : core.cmp.PartialEq U U)
  (cmpPartialEqInst1 : core.cmp.PartialEq T T) :
  (U × T) → (U × T) → Result Bool :=
  fun p q => do
    let b ← Pair.Insts.CoreCmpPartialEqPair.eq cmpPartialEqInst
      cmpPartialEqInst1 p q
    ok (!b)

/-- [core::tuple::{impl core::cmp::PartialOrd<(U, T)> for (U, T)}::partial_cmp]:
    Lexicographic, as in Rust. -/
@[rust_fun
  "core::tuple::{core::cmp::PartialOrd<(@U, @T), (@U, @T)>}::partial_cmp"]
def Pair.Insts.CoreCmpPartialOrdPair.partial_cmp
  {U : Type} {T : Type} (cmpPartialOrdInst : core.cmp.PartialOrd U U)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd T T) :
  (U × T) → (U × T) → Result (Option Ordering) :=
  fun p q => do
    let o ← cmpPartialOrdInst.partial_cmp p.1 q.1
    match o with
    | some Ordering.eq => cmpPartialOrdInst1.partial_cmp p.2 q.2
    | _ => ok o

/-- [core::tuple::{impl core::cmp::Ord for (U, T)}::cmp]:
    Lexicographic, as in Rust. -/
@[rust_fun "core::tuple::{core::cmp::Ord<(@U, @T)>}::cmp"]
def Pair.Insts.CoreCmpOrd.cmp
  {U : Type} {T : Type} (cmpOrdInst : core.cmp.Ord U) (cmpOrdInst1 :
  core.cmp.Ord T) :
  (U × T) → (U × T) → Result Ordering :=
  fun p q => do
    let o ← cmpOrdInst.cmp p.1 q.1
    match o with
    | Ordering.eq => cmpOrdInst1.cmp p.2 q.2
    | _ => ok o

/-! ## std::collections / std::hash -/

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::get]:
    Association-list lookup through `Borrow` and `Eq` (hashing unused). -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get"]
def std.collections.hash.map.HashMap.get
  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher :
  Type} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 :
  core.hash.Hash Q) (corecmpEqInst1 : core.cmp.Eq Q) :
  std.collections.hash.map.HashMap K V S A → Q → Result (Option V) :=
  fun m q =>
    TreeAux.lookup coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq
      m q

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::insert]: -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::insert"]
def std.collections.hash.map.HashMap.insert
  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher) :
  std.collections.hash.map.HashMap K V S A → K → V → Result ((Option V)
    × (std.collections.hash.map.HashMap K V S A)) :=
  fun m k v => TreeAux.insert corecmpEqInst.partialEqInst.eq m k v

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::finish]:
    Hasher state is `Unit`; the returned hash value is never observed. -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
  : std.hash.random.DefaultHasher → Result Std.U64 :=
  fun _ => ok 0#u64

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::write]: -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
  :
  std.hash.random.DefaultHasher → Slice Std.U8 → Result
    std.hash.random.DefaultHasher :=
  fun _ _ => ok ()

/-- [std::hash::random::{impl core::hash::BuildHasher<std::hash::random::DefaultHasher> for std::hash::random::RandomState}::build_hasher]: -/
@[rust_fun
  "std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher"]
def
  std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
  : std.hash.random.RandomState → Result std.hash.random.DefaultHasher :=
  fun _ => ok ()

/-- [alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<K, V, A>}::get]:
    Association-list lookup through `Borrow` and `Ord`. -/
@[rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::get"]
def alloc.collections.btree.map.BTreeMap.get
  {K : Type} {V : Type} {A : Type} {Q : Type} (corecloneCloneInst :
  core.clone.Clone A) (coreborrowBorrowInst : core.borrow.Borrow K Q)
  (corecmpOrdInst : core.cmp.Ord K) (corecmpOrdInst1 : core.cmp.Ord Q) :
  alloc.collections.btree.map.BTreeMap K V A → Q → Result (Option V) :=
  fun m q =>
    TreeAux.lookup coreborrowBorrowInst.borrow
      (fun a b => do
        let o ← corecmpOrdInst1.cmp a b
        match o with
        | Ordering.eq => ok true
        | _ => ok false)
      m q

/-! ## alloy_primitives (Hash256 = FixedBytes 32) -/

/-- [alloy_primitives::bits::fixed::{impl core::clone::Clone for alloy_primitives::bits::fixed::FixedBytes<N>}::clone]: -/
@[rust_fun
  "alloy_primitives::bits::fixed::{core::clone::Clone<alloy_primitives::bits::fixed::FixedBytes<@N>>}::clone"]
def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCloneClone.clone
  {N : Std.Usize} :
  alloy_primitives.bits.fixed.FixedBytes N → Result
    (alloy_primitives.bits.fixed.FixedBytes N) := ok

/-- [alloy_primitives::bits::fixed::{impl core::cmp::PartialEq<alloy_primitives::bits::fixed::FixedBytes<N>> for alloy_primitives::bits::fixed::FixedBytes<N>}::eq]:
    Byte-wise equality. -/
@[rust_fun
  "alloy_primitives::bits::fixed::{core::cmp::PartialEq<alloy_primitives::bits::fixed::FixedBytes<@N>, alloy_primitives::bits::fixed::FixedBytes<@N>>}::eq"]
def
  alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpPartialEqFixedBytes.eq
  {N : Std.Usize} :
  alloy_primitives.bits.fixed.FixedBytes N →
    alloy_primitives.bits.fixed.FixedBytes N → Result Bool :=
  fun x y => ok (decide (x.val = y.val))

/-- [alloy_primitives::bits::fixed::{impl core::cmp::Eq for alloy_primitives::bits::fixed::FixedBytes<N>}::assert_fields_are_eq]: -/
@[rust_fun
  "alloy_primitives::bits::fixed::{core::cmp::Eq<alloy_primitives::bits::fixed::FixedBytes<@N>>}::assert_fields_are_eq"]
def
  alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCmpEq.assert_fields_are_eq
  {N : Std.Usize} : alloy_primitives.bits.fixed.FixedBytes N → Result Unit :=
  fun _ => ok ()

/-- [alloy_primitives::bits::fixed::{impl core::hash::Hash for alloy_primitives::bits::fixed::FixedBytes<N>}::hash]:
    Faithfully feeds the bytes to the hasher (inert for our hashers). -/
@[rust_fun
  "alloy_primitives::bits::fixed::{core::hash::Hash<alloy_primitives::bits::fixed::FixedBytes<@N>>}::hash"]
def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreHashHash.hash
  {__H : Type} {N : Std.Usize} (corehashHasherInst : core.hash.Hasher __H) :
  alloy_primitives.bits.fixed.FixedBytes N → __H → Result __H :=
  fun x h => corehashHasherInst.write h (Array.to_slice x)

/-- [alloy_primitives::bits::fixed::{impl core::default::Default for alloy_primitives::bits::fixed::FixedBytes<N>}::default]:
    All zeroes. -/
@[rust_fun
  "alloy_primitives::bits::fixed::{core::default::Default<alloy_primitives::bits::fixed::FixedBytes<@N>>}::default"]
def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreDefaultDefault.default
  (N : Std.Usize) : Result (alloy_primitives.bits.fixed.FixedBytes N) :=
  ok (Array.repeat N 0#u8)

/-- [alloy_primitives::bits::fixed::{impl core::fmt::Debug for alloy_primitives::bits::fixed::FixedBytes<N>}::fmt]:
    Formatting output is unobservable (`Formatter` is opaque); a no-op. -/
@[rust_fun
  "alloy_primitives::bits::fixed::{core::fmt::Debug<alloy_primitives::bits::fixed::FixedBytes<@N>>}::fmt"]
def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreFmtDebug.fmt
  {N : Std.Usize} :
  alloy_primitives.bits.fixed.FixedBytes N → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ f => ok (.Ok (), f)

/-- [alloy_primitives::bits::fixed::{alloy_primitives::bits::fixed::FixedBytes<N>}::ZERO] -/
@[rust_const
  "alloy_primitives::bits::fixed::{alloy_primitives::bits::fixed::FixedBytes<@N>}::ZERO"]
def alloy_primitives.bits.fixed.FixedBytes.ZERO (N : Std.Usize)
  : Result (alloy_primitives.bits.fixed.FixedBytes N) :=
  ok (Array.repeat N 0#u8)

/-- [alloy_primitives::bits::fixed::{alloy_primitives::bits::fixed::FixedBytes<N>}::is_zero]: -/
@[rust_fun
  "alloy_primitives::bits::fixed::{alloy_primitives::bits::fixed::FixedBytes<@N>}::is_zero"]
def alloy_primitives.bits.fixed.FixedBytes.is_zero
  {N : Std.Usize} : alloy_primitives.bits.fixed.FixedBytes N → Result Bool :=
  fun x => ok (x.val.all (fun b => b == 0#u8))

/-! ## lock_api / parking_lot

The `RwLock` model is the protected value (see `TypesExternal.lean`); the lock
operations are pure plumbing. -/

/-- [lock_api::rwlock::{lock_api::rwlock::RwLock<R, T>}::new]: -/
@[rust_fun "lock_api::rwlock::{lock_api::rwlock::RwLock<@R, @T>}::new"]
def lock_api.rwlock.RwLock.new
  {R : Type} {T : Type} {Clause0_GuardMarker : Type} (RawRwLockInst :
  lock_api.rwlock.RawRwLock R Clause0_GuardMarker) :
  T → Result (lock_api.rwlock.RwLock R T) := ok

/-- [lock_api::rwlock::{lock_api::rwlock::RwLock<R, T>}::read]: -/
@[rust_fun "lock_api::rwlock::{lock_api::rwlock::RwLock<@R, @T>}::read"]
def lock_api.rwlock.RwLock.read
  {R : Type} {T : Type} {Clause0_GuardMarker : Type} (RawRwLockInst :
  lock_api.rwlock.RawRwLock R Clause0_GuardMarker) :
  lock_api.rwlock.RwLock R T → Result (lock_api.rwlock.RwLockReadGuard R T
    Clause0_GuardMarker) := ok

/-- [lock_api::rwlock::{lock_api::rwlock::RwLock<R, T>}::get_mut]: -/
@[rust_fun "lock_api::rwlock::{lock_api::rwlock::RwLock<@R, @T>}::get_mut"]
def lock_api.rwlock.RwLock.get_mut
  {R : Type} {T : Type} {Clause0_GuardMarker : Type} (RawRwLockInst :
  lock_api.rwlock.RawRwLock R Clause0_GuardMarker) :
  lock_api.rwlock.RwLock R T → Result (T × (T → lock_api.rwlock.RwLock R
    T)) :=
  fun l => ok (l, fun t => t)

/-- [lock_api::rwlock::{impl core::fmt::Debug for lock_api::rwlock::RwLock<R, T>}::fmt]: -/
@[rust_fun
  "lock_api::rwlock::{core::fmt::Debug<lock_api::rwlock::RwLock<@R, @T>>}::fmt"]
def lock_api.rwlock.RwLock.Insts.CoreFmtDebug.fmt
  {R : Type} {T : Type} {Clause0_GuardMarker : Type} (RawRwLockInst :
  lock_api.rwlock.RawRwLock R Clause0_GuardMarker) (corefmtDebugInst :
  core.fmt.Debug T) :
  lock_api.rwlock.RwLock R T → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ f => ok (.Ok (), f)

/-- [lock_api::rwlock::{impl core::ops::deref::Deref<T> for lock_api::rwlock::RwLockReadGuard<'a, R, T, Clause0_GuardMarker>}::deref]: -/
@[rust_fun
  "lock_api::rwlock::{core::ops::deref::Deref<lock_api::rwlock::RwLockReadGuard<'a, @R, @T, @Clause0_GuardMarker>, @T>}::deref"]
def lock_api.rwlock.RwLockReadGuard.Insts.CoreOpsDerefDeref.deref
  {R : Type} {T : Type} {Clause0_GuardMarker : Type} (RawRwLockInst :
  lock_api.rwlock.RawRwLock R Clause0_GuardMarker) :
  lock_api.rwlock.RwLockReadGuard R T Clause0_GuardMarker → Result T := ok

/-- [parking_lot::raw_rwlock RawRwLock impl]: lock state is invisible in a
    sequential model; locking always succeeds. -/
@[rust_fun
  "parking_lot::raw_rwlock::{lock_api::rwlock::RawRwLock<parking_lot::raw_rwlock::RawRwLock, lock_api::GuardNoSend>}::unlock_shared"]
def
  parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend.unlock_shared
  : parking_lot.raw_rwlock.RawRwLock → Result Unit :=
  fun _ => ok ()

@[rust_fun
  "parking_lot::raw_rwlock::{lock_api::rwlock::RawRwLock<parking_lot::raw_rwlock::RawRwLock, lock_api::GuardNoSend>}::try_lock_shared"]
def
  parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend.try_lock_shared
  : parking_lot.raw_rwlock.RawRwLock → Result Bool :=
  fun _ => ok true

@[rust_fun
  "parking_lot::raw_rwlock::{lock_api::rwlock::RawRwLock<parking_lot::raw_rwlock::RawRwLock, lock_api::GuardNoSend>}::lock_shared"]
def
  parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend.lock_shared
  : parking_lot.raw_rwlock.RawRwLock → Result Unit :=
  fun _ => ok ()

@[rust_fun
  "parking_lot::raw_rwlock::{lock_api::rwlock::RawRwLock<parking_lot::raw_rwlock::RawRwLock, lock_api::GuardNoSend>}::unlock_exclusive"]
def
  parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend.unlock_exclusive
  : parking_lot.raw_rwlock.RawRwLock → Result Unit :=
  fun _ => ok ()

@[rust_fun
  "parking_lot::raw_rwlock::{lock_api::rwlock::RawRwLock<parking_lot::raw_rwlock::RawRwLock, lock_api::GuardNoSend>}::try_lock_exclusive"]
def
  parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend.try_lock_exclusive
  : parking_lot.raw_rwlock.RawRwLock → Result Bool :=
  fun _ => ok true

@[rust_fun
  "parking_lot::raw_rwlock::{lock_api::rwlock::RawRwLock<parking_lot::raw_rwlock::RawRwLock, lock_api::GuardNoSend>}::lock_exclusive"]
def
  parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend.lock_exclusive
  : parking_lot.raw_rwlock.RawRwLock → Result Unit :=
  fun _ => ok ()

@[rust_const
  "parking_lot::raw_rwlock::{lock_api::rwlock::RawRwLock<parking_lot::raw_rwlock::RawRwLock, lock_api::GuardNoSend>}::INIT"]
def
  parking_lot.raw_rwlock.RawRwLock.Insts.Lock_apiRwlockRawRwLockGuardNoSend.INIT
  : Result parking_lot.raw_rwlock.RawRwLock :=
  ok ()

/-! ## triomphe

`Arc T` is modelled as `T` (see `TypesExternal.lean`): after
functionalization, sharing is invisible and the safe API is the identity. -/

/-- [triomphe::arc::{triomphe::arc::Arc<T>}::new]: -/
@[rust_fun "triomphe::arc::{triomphe::arc::Arc<@T>}::new"]
def triomphe.arc.Arc.new {T : Type} : T → Result (triomphe.arc.Arc T) := ok

/-- [triomphe::arc::{triomphe::arc::Arc<T>}::ptr_eq]:
    Pointer identity is precisely the information the functional model erases,
    so this is opaque rather than defined; `ptr_eq_spec` below is the trusted
    characterization. -/
@[rust_fun "triomphe::arc::{triomphe::arc::Arc<@T>}::ptr_eq"]
opaque triomphe.arc.Arc.ptr_eq
  {T : Type} : triomphe.arc.Arc T → triomphe.arc.Arc T → Result Bool

/-- Trusted spec for `Arc::ptr_eq`: it always returns (it cannot fail or
    diverge), and a `true` result implies the two values are equal (same
    allocation ⇒ same value). A `false` result carries no information. -/
axiom triomphe.arc.Arc.ptr_eq_spec {T : Type}
    (x y : triomphe.arc.Arc T) :
  ∃ b, triomphe.arc.Arc.ptr_eq x y = ok b ∧ (b = true → x = y)

/-- [triomphe::arc::{impl core::clone::Clone for triomphe::arc::Arc<T>}::clone]:
    Cloning an `Arc` only bumps the refcount: the identity on values. -/
@[rust_fun
  "triomphe::arc::{core::clone::Clone<triomphe::arc::Arc<@T>>}::clone"]
def triomphe.arc.Arc.Insts.CoreCloneClone.clone
  {T : Type} : triomphe.arc.Arc T → Result (triomphe.arc.Arc T) := ok

/-- [triomphe::arc::{impl core::ops::deref::Deref<T> for triomphe::arc::Arc<T>}::deref]: -/
@[rust_fun
  "triomphe::arc::{core::ops::deref::Deref<triomphe::arc::Arc<@T>, @T>}::deref"]
def triomphe.arc.Arc.Insts.CoreOpsDerefDeref.deref
  {T : Type} : triomphe.arc.Arc T → Result T := ok

/-- [triomphe::arc::{impl core::cmp::PartialEq<triomphe::arc::Arc<T>> for triomphe::arc::Arc<T>}::ne]:
    Delegates to the pointee's `PartialEq` (as triomphe's impl does). -/
@[rust_fun
  "triomphe::arc::{core::cmp::PartialEq<triomphe::arc::Arc<@T>, triomphe::arc::Arc<@T>>}::ne"]
def triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.ne
  {T : Type} (corecmpPartialEqInst : core.cmp.PartialEq T T) :
  triomphe.arc.Arc T → triomphe.arc.Arc T → Result Bool :=
  corecmpPartialEqInst.ne

/-- [triomphe::arc::{impl core::cmp::PartialEq<triomphe::arc::Arc<T>> for triomphe::arc::Arc<T>}::eq]: -/
@[rust_fun
  "triomphe::arc::{core::cmp::PartialEq<triomphe::arc::Arc<@T>, triomphe::arc::Arc<@T>>}::eq"]
def triomphe.arc.Arc.Insts.CoreCmpPartialEqArc.eq
  {T : Type} (corecmpPartialEqInst : core.cmp.PartialEq T T) :
  triomphe.arc.Arc T → triomphe.arc.Arc T → Result Bool :=
  corecmpPartialEqInst.eq

/-- [triomphe::arc::{impl core::fmt::Debug for triomphe::arc::Arc<T>}::fmt]: -/
@[rust_fun "triomphe::arc::{core::fmt::Debug<triomphe::arc::Arc<@T>>}::fmt"]
def triomphe.arc.Arc.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) :
  triomphe.arc.Arc T → core.fmt.Formatter → Result ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter) :=
  corefmtDebugInst.fmt
