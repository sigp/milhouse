# Charon/Aeneas bugs encountered while extracting milhouse

Notes from extracting the `milhouse::tree` subset to Lean (July 2026), for
filing upstream. Versions used:

- charon: `cb50ff16` (vendored in the aeneas checkout)
- aeneas: `b59d5188` (2026-07-17)
- Extraction command: see `scripts/aeneas-extract.sh`; run against the
  `aeneas` branch of milhouse.

Issue trackers: <https://github.com/AeneasVerif/charon/issues>,
<https://github.com/AeneasVerif/aeneas/issues>.

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
**Status:** worked around by excluding Tree's `Debug` and `PartialEq` impls.

For a recursive type (`Tree` contains `Arc<Tree<T>>`), the derived
`Debug`/`PartialEq` impls generate a method body that references the trait
impl *struct* (e.g. for `Dyn.mk` in the `Debug` case) before that struct is
defined, and no mutual block or `impl_def` is emitted to tie the knot:

```
error: Tree/Funs.lean:677:9: Unknown constant `milhouse.tree.Tree.Insts.CoreFmtDebug`
error: Tree/Funs.lean:740:11: Unknown constant `milhouse.tree.Tree.Insts.CoreCmpPartialEqTree`
```

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
**Status:** unresolved for handle dereferencing and materializing mutation;
the extraction includes `get_cow`, `Cow::with_max_index`, and `CowOnMut::run`.

Expanding the extraction roots to `milhouse::cow` fails when translating the
`Deref::deref` implementations for `BTreeCow` and `VecCow`. Returning the
immutable variant's borrowed value raises `Unreachable`. Equivalent explicit
dereferences (`*value` and `&**value`) fail as well. Translating the `make_mut`
methods also raises `Unreachable` and `Could not find var for symbolic value`
errors while handling the borrowed fields and returned mutable reference.

The `into_mut` closures fail with `Can't end abstraction 17 as it is set as
non-endable`. An explicit match/early-return formulation avoids that particular
closure failure, but does not resolve the other handle-method failures; that
trial rewrite was not retained. Excluding individual methods from the full
module root also leaves generated trait implementations referencing missing
translated methods. The script instead selects just the supported helpers.

`Tree/Cow/Value.lean` observes the carried value in the already-extracted data
type. `Tree/ProgressiveList/CopyOnWrite.lean` proves lookup and unchanged-release
behavior under generic map laws using that observer. This is not a replacement
model or a proof of Rust `Deref`, `make_mut`, or `into_mut`. Those translation
bridges and the resulting end-to-end mutation proof remain outstanding. No
Aeneas source changes or axioms for the missing methods have been introduced.

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

## Also of note (not bugs)

- Aeneas's custom `do`-elaborator rejects `if ← e then ...`, `match ← e
  with`, and nested `(← e)` forms that standard Lean `do` accepts —
  hand-written external models must use explicit `let x ← e` binds.
- Hand-written models for external *types* that occur inside generated
  inductives/structures (e.g. `Arc` inside `Tree`) must be `@[reducible]`,
  otherwise the auto-derived `SizeOf` instances fail to elaborate.
