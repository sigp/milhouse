# Nested MaxMap loses its inner CoW callback

This native Rust reproducer demonstrates stale inner maximum metadata for
the valid type `MaxMap<MaxMap<M>>`. It does not use Aeneas or Lean models.
The baseline is commit `3575ee6`; the accompanying patch only appends tests
inside `src/update_map.rs`, where the private inner map can be inspected.
Map construction and mutation use existing methods without changing any
private state directly.

Start with key 3 in both wrappers and acquire a fallback CoW handle at key
17. After either `into_mut` or `make_mut`, the inserted value is observable
through both wrappers and the outer maximum is 17, but the inner maximum
remains 3. Both supplied-value and lazy acquisition reproduce this with
`VecMap<u64>` and `BTreeMap<usize, u64>` backends: eight failing cases.
The read-only/direct-mutation control passes: read-only CoW leaves both
caches at 3, while `get_mut_with` and ordinary insertion update both caches.

The failure is an internal cache-invariant violation. This reproducer does
not demonstrate an incorrect outer lookup, outer maximum, or public list
length. The usual single `MaxMap<VecMap<T>>` default does not have a second
callback to overwrite.

## Cause and proof consequence

`Cow::with_max_index` assigns `on_mut.max_index = Some((max_index, index))`.
An outer MaxMap thereby discards the callback installed by an inner MaxMap.
The eventual mutation runs only the outer callback. The inner borrow ends
without recording the new key.

This matches the proved `Cow.releaseIndex` continuation: it restores the
original inner callback unchanged. The `Cow.Written` contract, in contrast,
records that callback. Therefore an outer filled footprint cannot in general
be passed directly to the original inner handle's `Written` contract.
The existing outer-maximum theorem and conditional list theorems remain
valid; they do not claim that this inner contract transfers automatically.

Assuming every inner handle has no callback would exclude nested MaxMap
configurations instead of repairing their behavior. A repair must address
callback composition while retaining delayed, one-shot recording and the
performance of the common single-wrapper case. Proof changes were stopped
and the Rust bug was raised under the repository's `AGENTS.md` instruction.

## Reproduce

From the repository root, create an isolated checkout on the same filesystem:

```sh
root_dir="$PWD"
probe_dir=$(mktemp -d "$root_dir/aeneas-lean/.lake/nested-max-map-cow.XXXXXX")
git worktree add --detach "$probe_dir/repo" 3575ee6
cp Cargo.lock "$probe_dir/repo/Cargo.lock"
git -C "$probe_dir/repo" apply \
  "$root_dir/aeneas-lean/reproducers/nested_max_map_cow/reproducer.patch"
cd "$probe_dir/repo"
CARGO_TARGET_DIR="$root_dir/aeneas-lean/.lake/sept7-cargo-target" \
CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 \
cargo +nightly-2026-08-18 test --locked --offline --lib nested_cow_metadata_probe
```

Expected exit code: **101**, with **1 passed, 8 failed, 324 filtered out**.
Each failure reports the inner maximum as `Some(3)`, expected `Some(17)`.
The patch is a diagnostic, not a test added to the production passing suite.
`report.json` records source/patch/lockfile hashes and the observed result.
The full session log is `.lake/nested-max-map-cow-probe/native.log`.

After inspecting the result, remove only this diagnostic checkout:

```sh
cd "$root_dir"
git worktree remove --force "$probe_dir/repo"
rmdir "$probe_dir"
```
