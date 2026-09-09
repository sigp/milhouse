# Charon/Aeneas bugs encountered while extracting milhouse

Notes from extracting the `milhouse::tree` subset to Lean (July 2026), for
filing upstream. Versions used:

- charon: `cb50ff16` (vendored in the aeneas checkout)
- aeneas: `b59d5188` (2026-07-17)
- Extraction command: see `scripts/aeneas-extract.sh`; run against the
  `aeneas` branch of milhouse.

Issue trackers: <https://github.com/AeneasVerif/charon/issues>,
<https://github.com/AeneasVerif/aeneas/issues>.

Scope revision (2026-09-09): Debug and Serde implementations, including
Serde-based context deserialization, are out of scope for the
[ProgressiveList proof goal](PROGRESSIVE_LIST_PROOFS.md#goal-and-scope).
The corresponding findings in issues 5, 20, and 22 are retained as historical
diagnostics, not outstanding goal obligations. SSZ codec and error-formatting
proofs remain in scope.

## 1. Charon: `Iterator::cloned`/`copied` break `--remove-associated-types`

**Stage:** charon (`--preset=aeneas`).
**Status:** worked around in milhouse commit `dd4b912`.

If any code in the crate calls `Iterator::cloned` (or `copied`), charon
translates the provided method, whose where-clause is
`Self: Iterator<Item = &'a T>`. After the aeneas preset's associated-type
removal turns `Iterator` into `Iterator<Item>`, that clause must unify with
the unique `Iterator` impl of every in-scope iterator — which fails for any
iterator whose `Item` is not literally `&'a T`:

```
error: Type error after transformations:
       Mismatched trait clause:
       expected: TraitClause0_1: (Counter: Iterator<&'a T>)
            got: impl_Iterator_for_Counter: Iterator<Counter, u32>
```

Rustc accepts this (the method is simply not callable on such iterators).

Minimal repro (fails only when `use_cloned` is present):

```rust
pub struct Counter { count: u32 }

impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        self.count += 1;
        Some(self.count)
    }
}

pub fn use_cloned(v: &[u32]) -> Option<u32> {
    v.iter().cloned().next()
}
```

**Workaround:** replace `.cloned()`/`.copied()` with `.map(|x| x.clone())`.

## 2. Aeneas: uncaught exception in `ty_regions.add_region`

**Stage:** aeneas translation (whole-crate run only).
**Status:** worked around in `repeat_list` by consuming the two possible
`SmallVec` entries with `pop` instead of matching on `&layer[..]`.

On the full milhouse crate, aeneas previously aborted with an uncaught OCaml
exception (instead of the usual collected errors) while symbolically
executing `milhouse::repeat::repeat_list` (`src/repeat.rs:46`):

```
Raised at Aeneas__TypesUtils.ty_regions.add_region in file "llbc/TypesUtils.ml", lines 24-25
```

With newer Aeneas builds the same shared-slice pattern instead produced a
collected `Inconsistent projection: PtrMetadata` error and a partial Lean
file. Avoiding the shared slice removes both failures; focused Charon/Aeneas
translation of `repeat_list` now succeeds without placeholders.

## 3. Aeneas: internal error on `UpdateMap::is_empty` (provided trait method)

**Stage:** aeneas translation.
**Status:** worked around via `--exclude 'milhouse::update_map::UpdateMap::is_empty'`.

`Internal error: please file an issue` on the *signature* of a provided
trait method with a trivial body (`src/update_map.rs:32`):

```rust
pub trait UpdateMap<T>: ... {
    fn for_each_range<F, E>(&self, start: usize, end: usize, f: F) -> Result<(), E>
    where
        F: FnMut(usize, &T) -> ControlFlow<(), Result<(), E>>;
    ...
    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
```

Possibly related to the `FnMut`-bound generic method (`for_each_range`) in
the same trait.

## 4. Aeneas Lean backend: `FnMut` closures get a mismatched calling convention

**Stage:** Lean elaboration of generated code.
**Status:** worked around by excluding `Tree::with_updated_leaves` and
`PackedLeaf::update`.

For closures passed to `UpdateMap::for_each_range` (an `FnMut` bound), the
generated `FnOnce` impl binds a `call_once` function that has the *state
passing* (`FnMut`-style) signature:

```
error: Tree/Funs.lean:593:4: Type mismatch
    Usize × T → Result (ControlFlow Unit (Result Unit Error) × closure T U)
  closure T U → Usize × T → Result (ControlFlow Unit (Result Unit Error))
```

i.e. the emitted function returns `Output × Self` and is missing the leading
`Self` parameter expected by `core.ops.function.FnOnce.call_once`.
Source closures: `src/packed_leaf.rs:100`, `src/tree.rs:187` and `:192`.

## 5. Aeneas Lean backend: recursive derived impls emitted with forward references

**Stage:** Lean elaboration of generated code.
**Status:** `Debug` is out of scope for the proof goal and remains excluded
from extraction. The Debug findings below are historical. `PartialEq` is
extracted using concrete Arc-comparison helpers in milhouse (commit `89044cc`).

For a recursive type (`Tree` contains `Arc<Tree<T>>`), the derived
`Debug`/`PartialEq` impls generate a method body that references the trait
impl *struct* (e.g. for `Dyn.mk` in the `Debug` case) before that struct is
defined, and no mutual block or `impl_def` is emitted to tie the knot:

```
error: Tree/Funs.lean:677:9: Unknown constant `milhouse.tree.Tree.Insts.CoreFmtDebug`
error: Tree/Funs.lean:740:11: Unknown constant `milhouse.tree.Tree.Insts.CoreCmpPartialEqTree`
```

For equality, the retained inline `Tree::arc_eq` and
`ProgressiveTree::arc_eq` helpers perform `Arc::ptr_eq(left, right) ||
Self::eq(left, right)`. Educe's custom field-comparison attributes call these
helpers instead of constructing the recursive Arc trait dictionary. They
preserve the original pointer shortcut, comparison order, and cache omission;
Aeneas emits the actual recursive comparisons and helpers in mutual blocks.
The list's tree field uses the same progressive helper. Regression tests cover
nonreflexive values with shared subtrees and differently populated hash caches.
`Tree/Equality`, `Tree/ProgressiveTree/Equality`, and
`Tree/ProgressiveList/Equality` prove the actual emitted comparisons, including
shortcuts, structural characterization, and sequence soundness. No Aeneas
source change or replacement model of a milhouse equality method is used.

The concrete `ProgressiveList::fmt` probe at `47d6b81` adds a proof caller
with explicit `T: Value + Debug` and `U: UpdateMap<T> + Debug`, and removes
the binary `Tree` Debug exclusion. Charon and Aeneas finish successfully.
The emitted binary and progressive `fmt` bodies still construct their own
Debug dictionary before its declaration, through `Arc` fields in `Dyn.mk`.
Inlining the dictionary and arranging recursive definitions would address
that syntactic dependency, but would not by itself establish faithful public
formatting semantics:

- The local `milhouse_fmt` model deliberately supports only default-option
  SSZ error messages with a string buffer. It does not represent arbitrary
  formatter options or user-provided sinks. Its helpers currently cover one-
  and two-field error structs; the derived list/tree formatters also use
  three-field structs and tuple variants.
- The existing external `FixedBytes` and `RwLock` Debug models return the
  opaque built-in formatter unchanged. Redirecting generated dictionaries
  to `milhouse_fmt.Debug` also exposes this interface mismatch. Reusing these
  no-op bodies cannot prove visible cache formatting.
- Pinned `lock_api` 0.4.12, `src/rwlock.rs:1208`, uses `try_read` when
  formatting: it prints either the protected data or `<locked>`. The current
  value-only `RwLock` model has no state distinguishing these outcomes.
  Assuming unlocked caches would restrict the public method's behavior.

The probe is isolated; no generated Debug body, no-op output proof, or Rust
rewrite is retained in the production extraction. Full Debug correctness
needs faithful formatter and lock-observation models as well as a solution
to recursive dictionary emission. This is an extraction/model limitation,
not evidence of a bug in milhouse's derived Rust implementation.

The source inventory through `0ed21ba` also explicitly accounts for
`ProgressiveListIter` and `ProgressiveListIterCow`, which each derive Debug in
`src/progressive_list.rs`. Their formatters remain unextracted and unproved;
the list probe above does not establish an extraction result for either one.
Their actual backing-iterator and map dictionaries, index fields, and the
read-only iterator's length field must be retained. These derives are not gated
by the `debug` feature, which only changes the bounds on `Value`.

## 6. Aeneas Lean backend: `impl_def` fails on self-referential default method

**Stage:** Lean elaboration of generated code.
**Status:** worked around by a post-generation patch in
`scripts/aeneas-extract.sh`.

The `core::cmp::Eq` impl for tuples is emitted as an `impl_def` whose
`assert_fields_are_eq` field invokes the default method on the impl being
defined:

```lean
impl_def Pair.Insts.CoreCmpEq {U : Type} {T : Type} (cmpEqInst : core.cmp.Eq U)
  (cmpEqInst1 : core.cmp.Eq T) : core.cmp.Eq (U × T) := {
  partialEqInst := ...
  assert_fields_are_eq := core.cmp.Eq.assert_fields_are_eq.default
    (Pair.Insts.CoreCmpEq cmpEqInst cmpEqInst1)
}
```

which fails with:

```
error: Tree/Funs.lean:59:0: impl_def: could not resolve recursive fields: [assert_fields_are_eq]
```

Pulled in by `Tree::intra_rebase`'s `HashMap<(usize, Hash256), _>`. The
patch rewrites it to a plain `def` with `assert_fields_are_eq := fun _ => ok ()`
(the value the default resolves to).

## 7. Aeneas Lean backend: local bindings shadow module namespaces

**Stage:** Lean elaboration of generated code.
**Status:** worked around in milhouse by renaming the Rust bindings
(`Tree::clone`, commit `2606ab4`).

Generated code keeps Rust variable names, so a Rust binding named `leaf`
(from `Self::Leaf(leaf) => ...` in a crate that also has a `leaf` module)
shadows the `milhouse.leaf` namespace. A subsequent reference to the global
`leaf.Leaf.Insts.CoreCloneClone.clone` is then parsed as a field projection
on the local variable:

```
error: Tree/Funs.lean:831:11: Invalid field `Leaf`: The environment does not
contain `milhouse.leaf.Leaf.Leaf`, so it is not possible to project the field
`Leaf` from an expression
```

Generated identifiers referencing globals should be qualified (e.g. with
`_root_.`) or locals should be renamed on collision.

The `arbitrary` feature exposes the same issue in a generated trait: the first
field of `arbitrary.Arbitrary` is named `arbitrary`, shadowing the namespace
in later field types. `scripts/aeneas-qualify-arbitrary.py` fully qualifies
those type references within that single generated structure. The extraction
script applies this idempotent fix automatically; the field names, types,
and actual milhouse method bodies are preserved, with no Aeneas changes.

Feature extraction also uses explicit Tree method roots instead of the whole
Tree module. The broader root pulls in unrelated derived Arbitrary impls whose
thread-local recursion guards cause an unsupported mixed recursive declaration
group. The existing Tree method bodies remain selected. The pinned arbitrary
1.4.1 library is external: `Tree/Arbitrary/Models.lean` models its control-byte
Vec loop and trait defaults, including first-error input state and custom
element generators that replace the input. The ProgressiveList generator
itself and all four trait entry points are extracted through proof roots.

## 8. Aeneas: borrowed fallback closure cannot end an abstraction

**Stage:** Aeneas symbolic execution.
**Status:** worked around in `ProgressiveList::get` using an explicit match,
as in the existing `List::get` extraction.

The lazy fallback `self.updates.get(index).or_else(|| self.backing_get(index))`
fails while translating the closure with
`Can't end abstraction 6 as it is set as non-endable`.
Matching on the update lookup and calling `backing_get` only in the `None`
branch preserves the lookup order and avoids the borrowing closure. No
Aeneas changes are required.

The same failure occurs in `ProgressiveList::get_cow` (`Can't end abstraction
10 as it is set as non-endable`). Its workaround checks whether an update
already exists, reads the backing value only when needed, and delegates to
the branch's `UpdateMap::get_cow_with_value` helper. It adds a map lookup but
preserves lazy backing reads, does not allocate on read-only access, and uses
the existing copy-on-write maximum-index tracking.

## 9. Aeneas: copy-on-write handle methods fail on borrowed fields

**Stage:** Aeneas symbolic execution.
**Status:** consuming `Cow::into_mut` now extracts through concrete helpers;
handle dereferencing and borrowed `make_mut` remain unresolved. The extraction
also includes `get_cow`, `Cow::with_max_index`, and `CowOnMut::run`.

Expanding the extraction roots to `milhouse::cow` fails when translating the
`Deref::deref` implementations for `BTreeCow` and `VecCow`. Returning the
immutable variant's borrowed value raises `Unreachable`. Equivalent explicit
dereferences (`*value` and `&**value`) fail as well. Translating the `make_mut`
methods also raises `Unreachable` and `Could not find var for symbolic value`
errors while handling the borrowed fields and returned mutable reference.

The `into_mut` closures fail with `Can't end abstraction 17 as it is set as
non-endable`. An explicit match/early-return formulation avoids that particular
closure failure, but does not resolve the other handle-method failures; that
trial rewrite was not retained at that checkpoint. Excluding individual methods from the full
module root also leaves generated trait implementations referencing missing
translated methods. The script instead selects just the supported helpers.

`Tree/Cow/Value.lean` observes the carried value in the already-extracted data
type. `Tree/ProgressiveList/CopyOnWrite.lean` proves lookup and unchanged-release
behavior under generic map laws using that observer. This is not a replacement
model or a proof of Rust `Deref`, `make_mut`, or `into_mut`. Handle data alone
does not discharge these method specifications. No Aeneas source changes or
axioms for the missing methods have been introduced.

A later isolated consuming-path probe succeeds by moving each concrete
`into_mut` body into an inline inherent helper. `Cow::into_mut` calls those
helpers directly, while `CowTrait::into_mut` delegates to the same bodies.
This keeps the untranslatable `make_mut`/`Deref` dictionaries out of the
consuming call graph. Explicit entry matches avoid the original closure
failure. Explicit outer result matches also avoid a separate borrowed-`Try`
interface mismatch: Aeneas emits a `(ControlFlow, backward)` result while its
standard `Result::branch` model returns only `ControlFlow`. Namespace-safe
`inner`/`handle` bindings avoid issue 7. The public API, successful/error
mutation order, and number of clones are unchanged.

The complete extraction now includes the actual public `Cow::into_mut` and
its write-back continuation. `Tree/Cow/EntryModels.lean` supplies the reached
external vacant-entry insertion models; the former `Unit` placeholders now
retain the keyed exclusive slot and final stored value. Vector slots also
retain backing length, so the pinned `index - len + 1` growth checks and vector
size bound are preserved. The enclosing generic map continuation frames other
keys and accounts for occupancy. This is an external entry model, not an
opaque model of a milhouse operation. The isolated successful extraction and
Lean-elaboration probe is `/tmp/milhouse-cow-consuming-probe-iegnawzx/`.
The regenerated full Lean build passes (1,937 jobs), and all 329 release tests
with `arbitrary` pass, including explicit clone-count/nonidentity-clone,
occupied-handle, missing-entry, and maximum-index checks. Consuming mutation
proofs are now established in `Cow/Consuming.lean` and
`ProgressiveList/CopyOnWrite/Consuming.lean`, including actual in-bounds list
replacement through `get_cow` and `into_mut`. The completed proof checkpoint
passes 1,941 Lean build jobs; all nine new lemmas use only standard axioms.
Borrowed mutation and CoW iterator stepping retain their separate limitations.

A fresh isolated borrowed-path probe after the consuming checkpoint is in
`/tmp/milhouse-cow-borrowed-probe-z1n008ka/`. Concrete public callers reproduce
the original failures. Flattening `Cow::deref` into direct nested variant
matches removes inner trait calls but still fails on the immutable value.
With `-print-error-emitters -print-error-diagnostics`, the actual error is
`interp/InterpBorrowsCore.ml:629`: `lookup_loan` receives no matching loan.
The previously reported `Interp.ml:609` is the catch-and-report location.

For borrowed `make_mut`, an isolated rewrite uses inline inherent helpers,
explicit entry/result matches, and a final nonrecursive mutable-variant
match. Both concrete helpers, the outer method, and its caller still fail.
`symbolic/SymbolicToPureCore.ml:520` reports missing symbolic values;
`symbolic/SymbolicToPureValues.ml:896` rejects an `AEmpty`, `AProjLoans`, or
`AProjBorrows` case during backward projection. The diagnostic does not
identify which of those three constructors was encountered. Removing trait
dispatch and `Try` adapters therefore does not resolve this borrowed path.
The variants and `deref-diagnostic.log`/`make-diagnostic.log` are preserved in
the probe directory. No trial rewrite or partial generated body was retained
in production, and no Aeneas source was changed.

## 10. Aeneas Lean backend: borrowed `Option::take` and `Ord::max` model mismatch

**Stage:** Lean elaboration of generated code.
**Status:** avoided with equivalent direct updates in the milhouse metadata
helpers; extraction and the corresponding Lean proofs succeed.

The original `CowOnMut::run` takes its `Option<(&mut MaxIndexState, usize)>`
before updating the maximum. The generated use of `Option::take` expects a
triple containing the taken value, new option, and a backward continuation;
the built-in Lean model returns a pair. Updating through the borrowed option
first and then assigning `None` avoids that call. `record_insert` only compares
and assigns unsigned indices, so moving the clear past it does not change
successful, error, or panic behavior. The callback remains one-shot.

The original `MaxIndexState::record_insert` uses `usize::max`. Extracting it
introduces calls to `core.cmp.Ord.max.default` with an `Ord` dictionary, whereas
the library model expects the comparison function. The same mismatch also
appears in generated tuple and `Length` trait fields when that default method
is pulled in. An explicit `if index > *max_index` update avoids the default
method and retains the exact maximum-index semantics.

`Tree/Cow/Metadata.lean` proves exact maximum recording, callback clearing and
one-shot behavior, and unchanged attachment/release for the extracted helpers.
The existing Rust callback and map regression tests cover the corresponding
runtime paths. These local workarounds do not fix the handle-method limitations
in issue 9.

## 11. Aeneas: generic loop drops an input type retained by `IntoIterator`

**Stage:** Lean extraction after symbolic execution.
**Status:** avoided by moving the progressive build loop into an
`Iterator<Item = T>` helper, following the existing binary-list builder.

The original `ProgressiveTree::build_from_iter_with_len` builds directly in a
`for item in iter` loop, where `iter: impl IntoIterator<Item = T>`. The extracted
loop retains the iterator and element types but drops the original input type.
Its `IntoIterator` dictionary still requires that dropped type, so extraction
reports `Could not find: type_var_id: 1 from ExtractBase.Item` and emits partial
loop signatures with `sorry` in the missing type position.

`ProgressiveTreeBuilder::extend_from_iter` now accepts `impl Iterator<Item = T>`;
the public builder performs `into_iter()` before calling that helper. Builder
creation, item consumption, error propagation, and finalization keep their
original order. This avoids the dictionary dependency without allocating an
intermediate collection or changing Aeneas. The regenerated extraction has no
missing-type admissions.

Spine assembly also reaches `Vec::IntoIter::next_back`, which was absent from
the existing local standard-library models. The owning iterator model already
stores its remaining vector, so the new definition delegates to the existing
`Vec::pop` model and erases the allocator parameter as the forward iterator
model does. Reverse-iterator assembly remains extracted Rust; its order and
contents are proved in `Tree/ProgressiveTree/Builder/Spine.lean`.

## 12. Aeneas: selected trait methods require concrete callers

**Stage:** Lean extraction.
**Status:** avoided for `TryFrom<Vec<T>>`, borrowed `IntoIterator`, the selected
progressive-list iterator methods, and list `PartialEq` by making their actual
bodies reachable from concrete callers.

Selecting `{impl core::convert::TryFrom for
milhouse::progressive_list::ProgressiveList}::try_from` succeeds in Charon.
`tree.llbc` contains the local transparent method and the `TryFrom`
implementation, but Aeneas initially emitted neither the method nor the
trait instance. Selecting the whole implementation had the same result.
Changing `ProgressiveList::new` to delegate through `Self::try_from(vec)`
makes the method reachable and emits its actual body. The trait still delegates
to the same inherent `try_from_iter`, preserving construction and error behavior.
The cause of the root-selection behavior has not been isolated.

The SSZ `TryFromIter` method emits when selected directly. Both trait methods
have full indexed-constructor specifications in
`Tree/ProgressiveList/Construction/Traits.lean`, derived from the complete
inherent constructor proof. No replacement model or post-extraction body is
used for either method.

The selected `ProgressiveListIter::next` and `size_hint` methods likewise emit
when called from the explicit `to_vec` loop. `ExactSizeIterator::len` now has
an explicit implementation returning `self.size_hint().0`: the concrete size
hint always has equal lower and upper bounds, so this is equivalent to the
trait default. Calling `len` from `to_vec` exposes both actual method bodies.

Borrowed `IntoIterator` has an additional root-selection restriction: Charon
rejects `{impl core::iter::IntoIterator for
&milhouse::progressive_list::ProgressiveList}::into_iter` because implementation
roots only support named types. `to_vec` now calls `self.into_iter()`, whose
actual body delegates directly to `self.iter()`. This preserves the cursor,
allocation, and clone order while making the trait method reachable.
`Tree/ProgressiveList/Iter/Traits.lean` proves full merged-sequence enumeration
through that emitted body, and `ToVec.lean` uses the new trait theorem.

List `PartialEq::eq` likewise appears as a transparent local body in LLBC when
selected by its implementation root, but is omitted by Aeneas without a caller.
`src/proof_roots.rs` now contains a concrete `left == right` caller, compiled
only with `cfg(milhouse_aeneas)` by the extraction script. It exposes the actual
derived public method and trait instance without adding a production call or
changing comparison behavior. The proofs target that public method, not a
replacement body or an assumed result for the caller.

The inherited `Clone::clone_from` is also made reachable through a concrete
proof-only caller. Aeneas emits the actual ProgressiveList `Clone` dictionary
and selects its standard `clone_from` default. The existing Lean library
supports that default directly; no new postprocessing is needed. The method
clones the source list rather than calling the pending map's `clone_from`.
`Tree/ProgressiveList/Clone/From.lean` connects the emitted caller to the
trait method and proves source-sequence replacement, source backing/cache
preservation, the pending observer, and total success under only the source
map clone's relevant laws. No destination invariant is required. Production
Rust behavior, the external models, and Aeneas are unchanged.

## 13. Aeneas: progressive traversal borrows and collection adapters

**Stage:** symbolic execution and signature translation.
**Status:** avoided with inline traversal-step helpers and an explicit
collection loop in milhouse; the Aeneas checkout is unchanged.

The original `ProgressiveTreeIter::seek_to_subtree` loop fails on the match
of its current shared progressive node inside the mutable loop. Moving one
iteration into `seek_step` keeps those borrows inside a call and translates
successfully. Once `next` is reachable, its mutable inner-iterator borrow
fails similarly. Its inline `next_step` returns `ControlFlow`, allowing the
outer loop to repeat or return without carrying that borrow across iterations.
Both helpers preserve the original traversal, state changes, and arithmetic
order without allocating or replacing traversal with repeated indexed lookup.

The original `ProgressiveList::to_vec` uses `cloned().collect()`, which fails
in `SymbolicToPureTypes.translate_fun_sigs` while translating the generic
iterator adapter signatures. The explicit loop follows the existing binary
`List::to_vec` implementation, preserves value and clone order, and reserves
from the exact iterator length. The resulting extraction contains the actual
progressive and list iterator bodies without admissions. Its `Option::or`
call uses a concrete local standard-library model.

## 14. Aeneas `toStr`: native-evaluated default proof adds caller axioms

**Stage:** axiom audit of proofs over generated iterator definitions.
**Status:** avoided with explicit kernel-checked literal-size proofs in the
local extraction post-processing; the Aeneas checkout is unchanged.

The built-in `toStr` takes a proof that a string's byte size fits `U32.max`.
Its default argument uses `decide +native`. Generated panic messages omit the
argument, so even a proof of immediate iterator exhaustion inherits a generated
`_native.decide.ax_*` dependency from the recursive definition's body. This is
separate from the existing upstream `sorry` warnings.

The extraction script now supplies `(by rw [U32.max_eq]; cbv)` for each emitted
string literal. Kernel-checked evaluation computes the literal's byte size after
rewriting the opaque maximum constant. The strings, branches, and error behavior
are unchanged; only the proof argument is supplied explicitly. Axiom audits of
the iterator results check that no native-evaluation dependency remains.

## 15. Progressive `pop_front`: cloning adapters, early loop returns, and iterator fields

**Stage:** Charon transformations, Aeneas prepasses, and Lean elaboration.
**Status:** avoided with a concrete streaming iterator-to-builder helper in
milhouse; Aeneas is unchanged.

Selecting `ProgressiveList::pop_front` reproduces issue 1 on its
`self.iter_from(n)?.cloned()` adapter, followed by a signature-translation
failure in `SymbolicToPureTypes.translate_fun_sigs`.

Replacing the adapter with a cloning loop in `pop_front` exposes another
limitation: Aeneas reports `Early returns inside of loops are not supported yet`
for the fallible builder push when the function also finalizes and replaces the
list after the loop. Moving the fallible loop into its own helper allows the
prepass to translate the error exit.

A generic `Iterator<Item = &T>` helper then causes Aeneas to emit the full
`ProgressiveListIter` iterator dictionary. That dictionary has `size_hint` and
`rev` fields, which are absent from `Aeneas.Std`'s `Iterator` structure. The
already-extracted standalone methods remain usable.

The final helper is `ProgressiveListIter::extend_builder`: it consumes the
concrete cursor, calls `next` directly, clones each value, and pushes it into the
same `ProgressiveTreeBuilder` used by construction. `pop_front` finalizes only
after successful consumption and replaces the original list only after all
fallible stages succeed. This preserves streaming allocation, element and clone
order, and error restoration, without an intermediate vector or an opaque model
of a milhouse method. Fresh extraction and the full Lean build succeed, and all
315 release tests pass.

## 16. Aeneas: progressive CoW stepping loses borrowed symbolic values

**Stage:** symbolic execution.
**Status:** unresolved for `ProgressiveListIterCow::next_cow`; the actual
`iter_cow`, `iter_cow_from`, and shared constructor translate successfully.

Selecting `milhouse::progressive_list::_::next_cow` fails on the borrowed
fallback closure with `Can't end abstraction 16 as it is set as non-endable`,
then reports `Could not find var for symbolic value` while translating the
outer method. Passing the already-read backing value directly to
`UpdateMap::get_cow_with_value` removes the closure failure but leaves the
outer-method errors. An inline helper taking the mutable map, mutable index,
and optional borrowed backing value translates itself, but its caller still
fails with the same missing-symbolic-value error.

Neither trial rewrite is retained. The extraction selects the supported
constructors only. `Tree/ProgressiveList/IterCow/Construction.lean` establishes
the backing-suffix/merged-overlay cursor invariant, exact start and pending
state, bounds rejection, and constructor write-back behavior. These are
constructor specifications, not a proof of `next_cow` enumeration or of CoW
handle dereferencing/materializing mutation (issue 9). The full goal retains
those obligations; no opaque milhouse-method model, admission, or Aeneas source
change is used to replace them.

A further isolated trial in `/tmp/milhouse-cow-borrowed-probe-z1n008ka/`
passes the backing value to the existing closure-free `get_cow_with_value`
and replaces the option `?` with an explicit `Some`/`None` match. The cursor
still advances only on `Some`. The concrete public caller loses symbolic
value 14, and `next_cow` loses values 25, 26, 33, 38, and 39; Aeneas emits
only partial files. `progressive-next-explicit.rs` and `next-explicit.log`
preserve this trial. No production rewrite is retained. This confirms that
removing both the fallback closure and option adapter is insufficient.

## 17. External equality models must preserve Arc shortcuts and slice `ne` calls

**Stage:** external-model fidelity review and proof premise audit.
**Status:** corrected locally in commits `2d2ca69` and `89044cc`; Aeneas is
unchanged. These are modeling corrections, not changes to Rust equality.

The pinned `triomphe` 0.1.14 implementation (`src/arc.rs`, `PartialEq for
Arc<T>`) defines `eq` as pointer equality OR pointee equality, and `ne` as
pointer inequality AND pointee inequality. The earlier local model delegated
directly to the pointee operation, losing the shortcut for nonreflexive values
or failing comparisons. `Tree/FunsExternal.lean` now uses the existing
`Arc.ptr_eq` model before calling the pointee operation. `Tree/Arc/Equality.lean`
proves the shortcut cases and positive-equality soundness using the existing
trusted `Arc.ptr_eq_spec`; no new axiom was introduced.

In the pinned nightly-2026-06-01 Rust source, `alloc/src/vec/partial_eq.rs`
delegates vector comparison to slices. The generic loop in
`core/src/slice/cmp.rs` tests element `ne` and returns false at the first
difference. Aeneas's `PartialEqVec.eq` instead calls element `eq`, which requires
an unstated coherence law for custom `PartialEq` implementations. Its vector
`ne` model already follows the Rust loop. The local `milhouse_models.vec_eq`
negates that vector `ne`, and the extraction script redirects generated calls
to this faithful external model. No milhouse method body is replaced.

Consequently, successful packed rebase equality requires soundness of false
element `ne`, while unpacked leaf rebasing requires soundness of true element
`eq`. Both premises now appear explicitly in the public rebase content
theorems; structural backing preservation still requires neither. Derived
tree/list equality uses element `ne` throughout: its total specification needs
the corresponding complete comparison law, while positive-result soundness
needs only the false-`ne` implication and assumes no comparison termination.

## 18. SSZ encoding: iterator adapters and recursive default dictionaries

**Stage:** Lean elaboration of generated encoding bodies and trait dictionaries.
**Status:** avoided in milhouse with explicit streaming loops and identical
explicit SSZ defaults; all five progressive-list encoding methods now extract
and have metadata, exact size, and exact byte-output specifications.

The original variable-size calculation uses `map(...).sum()`, and `ssz_append`
uses `for item in self`. Making these methods reachable exposes adapter
closures and the full iterator dictionary, including fields missing from the
Aeneas iterator model (`map`, `sum`, `size_hint`, and `rev`). Explicit
`while let Some(item) = iter.next()` loops remove the adapters and dictionary
dependency. They retain the same initial iterator, traversal and element-call
order, left-to-right additions, streaming allocation, and encoder operations.

The list encoder's default `ssz_fixed_len` field then fails with
`impl_def: could not resolve recursive fields: [ssz_fixed_len]`. Providing the
same four-byte constant explicitly avoids the self-reference. The identical
`as_ssz_bytes` default is also explicit, calling the actual concrete
`ssz_append` on a new empty vector. Extraction-only callers in `proof_roots`
make every actual method reachable, as in issue 12. Neither default changes
encoding behavior or introduces an intermediate element vector.

`Tree/TypesExternal.lean` represents the external ethereum_ssz 0.10.0 encoder's
offset, borrowed output buffer, and variable payload. `Tree/Ssz/Models.lean`
defines reserve, four-byte offset writing, container construction, append, and
finalization with their exact borrowed-buffer continuations. The generic
element encoder remains the real extracted trait argument. The development
profile's offset assertion is explicit; `OffsetsFit` requires only the offsets
actually emitted to fit 32 bits. Allocation/capacity erasure follows the
existing Aeneas vector abstraction, with logical size overflow checked.

`Tree/Ssz/{Bytes,Encoder}.lean` proves those operations and canonical offset
layout. `Tree/ProgressiveList/Encode` proves complete traversal, exact fixed and
variable sizes, exact append bytes with destination-prefix preservation, and
owning output. The successful offset bounds also make the bytes agree with
release encoding; no assertion about out-of-range release behavior is needed.
All 19 new public results use only standard Lean axioms. Fresh extraction,
the full 1,851-job build, formatting, and all 319 release tests pass, including
new fixed/variable differential encoding tests with pending updates and
nonempty output buffers. No Aeneas source changes, admissions, new axioms, or
opaque models of milhouse encoding methods were introduced. Decode and the
other remaining API obligations remain separate work.

## 19. SSZ decoding: borrowed adapters and erased formatting arguments

**Stage:** translation and generated-signature/model fidelity review.
**Status:** worked around locally with a concrete streaming cursor and observable
default-formatting models; Aeneas is unchanged. Full decoding proofs remain in progress.

The fixed decoder's `map(T::from_ssz_bytes)` first fails with `Unimplemented`
on the function item and surrounding `process_results` closure. An explicit
closure allows translation, but generated calls through `ProcessResults`
return borrowed iterator state that the generic `Iterator`, `FnOnce`, and
`try_from_iter` signatures do not carry. Treating these generated files as a
successful model would discard the stored decode error or fail elaboration.

`src/ssz_items.rs` now supplies a concrete streaming cursor. Its variable
branch follows ethereum_ssz 0.10.0's parser: first-offset bounds precede
alignment checks, and each next offset is checked before the preceding payload
is decoded. `ProgressiveList::decode_ssz_items` builds directly without an
intermediate vector. Like `process_results`, a decode error stops consumption
but still finalizes the partial builder, including the successful default-map
call, before returning that error. Builder failures stop consumption. The
fixed and variable wrappers retain their different placement of builder-error
formatting relative to selecting the decode error.

The real `DecodeError` enum is included in extraction, replacing its former
unobserved Unit model. `Tree/Ssz/DecodeModels.lean` models the external
four-byte offset reader. `Tree/Formatting/Models.lean` retains deferred Debug
calls, literal bytes, and default placeholders, instead of Aeneas's Unit
formatting arguments. Generated formatter calls are redirected locally; the
actual derived milhouse Error formatter remains extracted. Only the reached
default-option fragment is supported; other format opcodes fail explicitly.
This is not a specification of arbitrary formatting flags or user sinks.

Fresh extraction and the complete 1,853-job proof build pass. All 322 release
tests pass, including comparison with the previous streaming decoder across
subtree boundaries, short chunks, truncated/modified offset tables, and
competing offset and payload errors. The decode metadata defaults are explicit
but unchanged, avoiding recursive trait dictionaries as in issue 18. No opaque
milhouse-method model or Aeneas source modification is introduced.

The subsequent decoding foundations add 14 public lemmas: exact decode metadata,
empty-input behavior/representation, zero-width rejection, short variable-prefix
errors, four-byte offset reading and byte roundtrip, UTF-8 literal conversion,
the actual derived Error formatter, and both exact builder-error messages.
These all audit to standard Lean axioms only, as does the complete extracted
decoder body; the existing Aeneas Slice/StringIter admissions are not inherited.
The full build now passes 1,858 jobs. General decoding sequence reconstruction
and full list roundtrip remain outstanding in the coverage ledger.

## 20. Serde serialization: mutually recursive external trait dictionaries

**Stage:** generated Lean types and elaboration.
**Status:** Serde serialization and deserialization, including the inherited
in-place default, are out of scope for the proof goal. The extraction and
protocol findings below are historical. Aeneas and production Rust are
unchanged; no opaque milhouse-method model is substituted.

Making the actual `ProgressiveList::serialize` body reachable through this
extraction-only caller reproduces the issue with pinned serde 1.0.217:

```rust
pub fn progressive_list_serialize<T: Value + serde::Serialize, U: UpdateMap<T>, S: serde::Serializer>(
    list: &ProgressiveList<T, U>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    serde::Serialize::serialize(list, serializer)
}
```

The existing script's Charon and Aeneas commands complete, but Aeneas warns
that the mutually recursive `Serialize`, `Serializer`, and seven compound
serializer traits will not type-check (`Translate.ml`, line 1203). Checking
the generated `Types.lean` confirms unknown `serde.ser.Serializer` and
compound serializer identifiers. `Serialize.serialize` takes a `Serializer`
dictionary, whose generic methods and compound serializers take `Serialize`
dictionaries in turn. This is a recursive trait interface, not the
self-referential default-method issue avoided for SSZ in issue 18.

The concrete generated milhouse method faithfully calls
`Serializer.collect_seq` with the actual borrowed `IntoIterator` implementation
and the element serialization dictionary. Adding
`--exclude 'serde::ser::Serialize::serialize'` leaves the cyclic trait fields
in the generated types and does not resolve the failure. The probe was run
with generated files in a temporary directory; no failed extraction output
or probe root is retained in the normal build.

A workaround must preserve custom `collect_seq` overrides, element
serialization behavior, errors, and the iterator's length hint. The pinned
default obtains `iterator_len_hint`, starts a sequence, serializes each element
until an error, and ends the sequence. Replacing the public method with this
manual loop would bypass a serializer's override and is not an equivalent
general Rust change. Likewise, erasing the element serialization dictionary
or assuming the result of the milhouse method would not establish the requested
correctness. If Serde is brought back into scope, a suitable external protocol
model and its precise laws would need discussion; the existing iterator
enumeration and exact-length proofs are available underneath. Deserialization
would need its own extraction/protocol work and is not claimed proved by this
probe.

### Ordinary deserialization: source dependency audit

The current public `ProgressiveList::deserialize` in `src/progressive_list.rs`
dispatches through `Deserializer::deserialize_seq` with the actual
`ProgressiveListVisitor`. Its `visit_seq` in `src/serde.rs` calls
`SeqAccess::next_element<T>` through `from_fn` and `itertools::process_results`,
feeding the real `ProgressiveList::try_from_iter`. In pinned serde 1.0.217,
`next_element<T>` takes a `Deserialize<T>` dictionary whose method in turn
takes a `Deserializer` dictionary. Thus the ordinary visitor reaches the
same recursive interface family demonstrated by the contextual extraction in
issue 22. This is a source dependency finding, not a fresh extraction result;
no equivalent failed probe or partial ordinary-deserialization model is added.

A faithful model must retain the actual `next_element` dispatch, including
possible overrides. Its default calls `next_element_seed(PhantomData)`, but
replacing the public call with that default would bypass overrides. Pinned
itertools 0.13.0 records a sequence error and presents it to the processor as
end-of-iteration; `process_results` returns the recorded error only after the
processor returns. Builder finalization and error formatting may therefore
run before that error is returned. An immediate-error loop would need to
preserve this order, in addition to the generic trait interface.

The public default `Deserialize::deserialize_in_place` is also out of scope.
ProgressiveList supplies no override; serde 1.0.217
calls the actual `deserialize` and assigns its result to the destination only
after success. This default remains unproved alongside ordinary deserialization.

## 21. Progressive hashing: parallel recursive groups, LazyLock, and shared cache writes

**Stage:** Aeneas translation and the external lock model.
**Status:** the actual ProgressiveList classification and two packing-rejection
methods are extracted and proved separately. Root computation, pending-update
rejection through the public root, and preservation by shared hash-cache writes
remain pending. Cache initialization and preservation through extracted
constructors, pending mutations, application, front removal, and rebasing are
proved separately; those operations do not perform shared cache writes.
No production hashing method, Aeneas source, or lock model has been changed.

A fresh root probe adds this extraction-only caller and removes the binary
`Tree::tree_hash` exclusion from the existing extraction command:

```rust
pub fn progressive_list_tree_hash_root<T: Value + Send + Sync, U: UpdateMap<T>>(
    list: &ProgressiveList<T, U>,
) -> tree_hash::Hash256 {
    tree_hash::TreeHash::tree_hash_root(list)
}
```

The actual root reaches both binary and progressive hashing. Aeneas reports
mixed mutually recursive functions and closure trait implementations for the
`rayon::join` calls (`src/tree.rs:581`, `src/progressive_tree.rs:342`), followed
by `Mixed-recursive declaration groups are not supported`. The external
`ethereum_hashing::ZERO_HASHES` global also fails with `Arrow types are not
supported yet`: its `LazyLock` type contains the default initializer function
pointer (pinned ethereum_hashing 0.8.0, `src/lib.rs:219`). Partial output from
this probe is not retained in the normal extraction.

Metadata-only callers need an explicit exclusion of the list's root method
with the current binary-hash exclusion; otherwise an unused progressive-hash
closure reaches Aeneas prepasses and produces an internal error. The normal
script now selects the three independent methods through concrete callers and
excludes the root. No opaque milhouse hashing method is introduced.

Even after the translation errors are addressed, shared cache effects need a
faithful model. The current `RwLock R T := T` representation is documented as
valid only for the existing subset without shared writes. The new write
signature would be `RwLock R T -> Result (WriteGuard R T * (WriteGuard R T ->
Unit))`: releasing an updated guard does not return an updated lock or shared
heap. Returning the old value and discarding writes would not model future
cache reads or aliases. A stateful/ghost-state account of shared caches and
parallel calls is needed before claiming root or cache correctness. Removing
parallelism alone does not address this issue and would change performance.

The standalone [shared-cache reproducer](reproducers/shared_cache/README.md)
now isolates this boundary without Rayon or `LazyLock`. Its native
read/write/read test passes. Aeneas `b59d5188` with Charon `cb50ff16` (LLBC
version 0.1.223) translates the body but drops the written argument and reuses
the pre-write read guard. Charon retains the value assignment; the generated
Lean result is independent of the new value for every implementation of the
pure external signatures. `-eval-drops` produces identical function output.
Thus supplying a different pure local lock model cannot recover the native
behavior. No available state-passing CLI option was found; trait calls are
classified as stateless and the duplicate-call pass documents its assumption
against stateful calls. The fixture retains only native source, dependency
pins, and reproduction instructions, not axiomatized probe output in the proof
library. Aeneas has not been changed.

## 22. Context deserialization: incomplete opaque visitor interface and recursive seed protocol

**Stage:** external protocol extraction, Aeneas loop translation, and Lean
trait elaboration.
**Status:** Serde-based context deserialization is out of scope for the proof
goal. The historical probe reaches the actual public list body, but its complete
sequence/seed protocol is not yet extractable. No probe root, partial generated
file, modified dependency, or opaque milhouse-method model is retained.

A concrete extraction-only caller of
`<ProgressiveList<T, U> as ContextDeserialize<'de, C>>::context_deserialize`
with `T: Value + ContextDeserialize<'de, C>`, `C: Clone`, `U: UpdateMap<T>`, and
`D: serde::Deserializer<'de>` reaches the real `src/context_deserialize.rs`
method. Enable `arbitrary,context_deserialize` in the normal Charon command
and add `--opaque 'context_deserialize'` for the pinned external library.
The generated list body calls the external contextual Vec generator, then
actual `ProgressiveList::try_from`, mapping constructor errors through
`serde::de::Error::custom` with the formatted error message.

This first extraction completes, and its generated types elaborate after the
existing Arbitrary qualification fix. However, `serde.de.Visitor` contains
only `expecting`: it has no `visit_seq` or element-producing operations. Thus
that interface cannot implement the actual contextual vector visitor. The
successful extraction is not evidence of a faithful sequence model or public
correctness, and returning an assumed vector would leave that obligation open.

Adding `--include 'context_deserialize::impls::core'` exposes the pinned 0.2.0
Vec visitor and seed bodies. The complete interface is mutually recursive:

```
DeserializeSeed.deserialize -> Deserializer.deserialize_seq
  -> Visitor.visit_seq -> SeqAccess.next_element_seed -> DeserializeSeed
```

Aeneas warns that these four recursive trait declarations will not type-check
(`Translate.ml:1203`). Direct Lean elaboration of the generated types, using
the existing external types and Arbitrary qualification fix, confirms unknown
`serde.de.Deserializer`, `Visitor`, `SeqAccess`, and `DeserializeSeed`
identifiers at the forward references. This reproduces the deserialization
side of the interface limitation in issue 20. Independently, translating the
external visitor's `while let` condition fails with `There should be no bottoms
in the value` (`context_deserialize-0.2.0/src/impls/core.rs:55`,
`interp/InterpExpressions.ml:55`).

A faithful workaround must preserve the caller's actual
`Deserializer.deserialize_seq` dispatch, the initial sequence size hint,
context cloning before **every** `next_element_seed` call (including the
terminal call), the exact cloned context passed into each seed, and the first
sequence/element error. Clone identity is not generally implied by the trait.
Fixing the loop alone leaves the recursive interface unresolved. The existing
constructor totality and representation proofs can be composed once this
external protocol is supported.

## Also of note (not bugs)

- Aeneas's custom `do`-elaborator rejects `if ← e then ...`, `match ← e
  with`, and nested `(← e)` forms that standard Lean `do` accepts —
  hand-written external models must use explicit `let x ← e` binds.
- Hand-written models for external *types* that occur inside generated
  inductives/structures (e.g. `Arc` inside `Tree`) must be `@[reducible]`,
  otherwise the auto-derived `SizeOf` instances fail to elaborate.
