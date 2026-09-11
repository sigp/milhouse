# Shared cache write extraction reproducer

This standalone crate isolates the shared-write limitation affecting milhouse's
hash caches. It does not modify production Rust, the normal extraction, the
proof library, or Aeneas. The native Rust behavior is expected; the unsupported
boundary is translation of interior mutation through a shared lock reference.

From this directory, with `CHARON` and `AENEAS` set to the corresponding built
executables:

```sh
cargo test --locked --offline
"$CHARON" cargo --preset=aeneas \
  --start-from 'milhouse_shared_cache_probe::read_write_read' \
  --dest-file probe.llbc -- --locked --offline
"$AENEAS" -backend lean -split-files -dest lean probe.llbc
"$AENEAS" -backend lean -split-files -eval-drops -dest lean-drops probe.llbc
diff -u lean/Funs.lean lean-drops/Funs.lean
```

The dependencies must already be cached for offline execution. `Cargo.lock`
fixes the complete dependency graph, including the same parking_lot 0.12.3 and
lock_api 0.4.12 versions as the production extraction checkpoint.

The native test passes: starting from a lock containing 7, writing 9 returns
`(7, 9)` and leaves 9 in the lock. Writing 11 through another lock initially
containing 7 returns `(7, 11)`. A subsequent call through the first lock also
observes its previous write.

With Aeneas `b59d5188` and Charon `cb50ff16` (LLBC version 0.1.223), both
translations complete and produce identical `Funs.lean` files. Charon's LLBC
retains the copy of the `value` parameter into the assignment. The Lean body
instead has this shape, with the generated fully qualified names abbreviated:

```lean
def read_write_read (lock : RwLock RawRwLock U64) (value : U64) :
    Result (U64 × U64) := do
  let readGuard ← RwLock.read rawRwLockInst lock
  let before ← ReadGuard.deref rawRwLockInst readGuard
  let (writeGuard, _) ← RwLock.write rawRwLockInst lock
  let _ ← WriteGuard.deref_mut rawRwLockInst writeGuard
  let after ← ReadGuard.deref rawRwLockInst readGuard
  ok (before, after)
```

The written `value` is unused, write-back continuations are discarded, and the
last dereference uses the read guard obtained before the write. Consequently,
for any implementation of these pure external interfaces, the generated
result is independent of `value`. A local lock model cannot restore the native
dependence on that parameter. In particular, the generated write interface
returns a guard and a continuation ending in `Unit`, with no updated shared
lock or heap.

This probe does not supply external Lean models or claim that the generated
templates constitute a verified program. No generated file belongs to the
production proof imports. It establishes a translation/model limitation even
without Rayon, recursive hashing, or `LazyLock`.

Read-only inspection of this Aeneas revision found no CLI state-passing option.
`src/llbc/FunsAnalysis.ml` treats trait calls as stateless; the duplicate-call
pass in `src/pure/PureMicroPassesGeneral.ml` explicitly notes that it would need
revision for stateful functions. `-eval-drops` does not change this example.
Faithful root hashing therefore needs further extraction support or an agreed
workaround that preserves shared cache writes. Removing parallelism alone
would not resolve this boundary.
