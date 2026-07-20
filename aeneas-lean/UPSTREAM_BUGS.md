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

On the full milhouse crate, aeneas aborts with an uncaught OCaml exception
(instead of the usual collected errors) while symbolically executing
`milhouse::repeat::repeat_list` (`src/repeat.rs:46`):

```
Raised at Aeneas__TypesUtils.ty_regions.add_region in file "llbc/TypesUtils.ml", lines 24-25
```

This kills the run before any Lean files are written. `-borrow-check` mode
crashes the same way. Not reachable from the `milhouse::tree` subset, so no
workaround was needed there.

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

## Also of note (not bugs)

- Aeneas's custom `do`-elaborator rejects `if ← e then ...`, `match ← e
  with`, and nested `(← e)` forms that standard Lean `do` accepts —
  hand-written external models must use explicit `let x ← e` binds.
- Hand-written models for external *types* that occur inside generated
  inductives/structures (e.g. `Arc` inside `Tree`) must be `@[reducible]`,
  otherwise the auto-derived `SizeOf` instances fail to elaborate.
