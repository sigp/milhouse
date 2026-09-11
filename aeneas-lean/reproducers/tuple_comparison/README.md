# Tuple inequality model regression

The pinned extraction toolchain is `nightly-2026-06-01`, rustc
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. Its
`library/core/src/tuple.rs` implements tuple `ne` using the element `ne`
methods, joined by short-circuiting `||`. Tuple `eq` instead calls element
`eq` and combines the results with `&&`.

The former `Pair.Insts.CoreCmpPartialEqPair.ne` model negated tuple `eq`.
That changes the called methods and can change failure, divergence, or
observable effects without an additional callback-equivalence assumption.
The corrected model preserves the actual `ne` dispatch and order.

From the repository root:

```sh
rustc +nightly-2026-06-01 --test aeneas-lean/reproducers/tuple_comparison/native.rs -o /tmp/milhouse-tuple-comparison-tests
/tmp/milhouse-tuple-comparison-tests
```

The four native tests cover both possible second results, a first true result
skipping a failing second comparison, and failure at either reached comparison.
Every element `eq` panics and records a distinct call, so accidentally negating
tuple equality fails these checks. The tests record the actual callback order.

From `aeneas-lean`, run:

```sh
lake build Tree.Tuple.Comparison
```

The six Lean lemmas characterize short-circuiting, exact second-call delegation,
first-call failure/divergence, and both successful Boolean results. They use no
relationship between `eq` and `ne` and no laws on unreached callbacks. They fail
against the former model; they are kernel proofs over the corrected model,
separate from the native evidence for Rust's callback protocol.

The later [tuple source comparison suite](../tuple_models/README.md) directly
extracts all four pinned pair-comparison bodies and proves them equal to the
local models for arbitrary callback results. Its four native tests extend
dispatch/order coverage to equality and both ordering operations.

The current ProgressiveList dependency inventory includes this tuple dictionary
only through the optional BTreeMap hash lookup under `apply_updates`. The
progressive update path passes `None` (`src/progressive_tree.rs`), and the
existing `Tree/BulkUpdate/Success.lean` proofs reduce `utils.opt_hash none`
without reaching map lookup or tuple comparison. This correction does not
establish the remaining model-fidelity audit or borrowed CoW obligations.
