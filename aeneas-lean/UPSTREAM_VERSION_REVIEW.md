# Aeneas upgrade review — 2026-09-10

Upstream contains relevant fixes, but none has yet been verified against our
exact borrowed-CoW failures. The latest release also breaks existing Lean
proof patterns. Keep the working pin while testing the candidates below.
This review changes no Rust, extracted definitions, proofs, tool pins, audit
version gates, or Aeneas sources.

## Versions compared

| Component | Working pin | Candidate before the Result change | Latest upstream checked |
| --- | --- | --- | --- |
| Aeneas commit | `b59d5188c082f704a418c7cb4e52ad69328002d1` | `7ebd01d1945570aef03bc76b47273ca1d1ff3c23` | `505b6ca35217e7be5c96c3e2f8045edfbdf47291` |
| Charon commit | `cb50ff16b9f1066b8a97dc06da704de2da2fa41c` | `85bba1f2a64ded1704586cdc26dfb62aeb4b7168` | `b104e24fea7d721b71e6c39fd70f26ff20bc0980` |
| Rust nightly | `2026-06-01` | `2026-08-18` | `2026-08-18` |
| Lean | `4.31.0` | `4.31.0` | `4.31.0` |

Latest upstream is 103 commits ahead of the working pin. The candidates are
the official Linux x86-64 bundles from releases
[`nightly-2026.09.08-7ebd01d`](https://github.com/AeneasVerif/aeneas/releases/tag/nightly-2026.09.08-7ebd01d)
and
[`nightly-2026.09.10-505b6ca`](https://github.com/AeneasVerif/aeneas/releases/tag/nightly-2026.09.10-505b6ca).
Their SHA-256 digests were checked against GitHub's release metadata:

```text
7ebd01d: 763c78dc8c596c557c4984e2ecccd30a9e0145dcbb3a9dd6b6f5eb67981056c1
505b6ca: 6a714d461e2c2c65b81f181763c27ea520b910ede40278829f6c0fda0eb9ba15
```

## Relevant fixes and remaining uncertainty

| Upstream change | Relevance and limits |
| --- | --- |
| [#1331: avoid visiting projections twice](https://github.com/AeneasVerif/aeneas/pull/1331), merged September 3 | Fixes traversal in `lookup_aproj_loans_opt` and partially addresses issue #1192. Our enum-reader reproducer fails in `lookup_loan`, a different function. This is a reason to retest, not evidence that our CoW problem is fixed. |
| [#1333: repair closure signature regions](https://github.com/AeneasVerif/aeneas/pull/1333), merged September 3 | Repairs erased closure lifetime arguments when the signature binds exactly one region. Potentially relevant to the VecMap insertion dependency failure; it does not establish support for all `try_fold` or nested-borrow signatures. |
| [#1131: filter Iterator implementation fields](https://github.com/AeneasVerif/aeneas/pull/1131), merged September 3 | Can omit implementation methods absent from the builtin trait model. Requires the new `-filter-trait-methods` flag, which defaults to off. Retest iterator-dependent extraction both with the existing flags and with this flag. |
| [#1286: repair default Ord min/max models](https://github.com/AeneasVerif/aeneas/pull/1286), merged September 3 | Relevant to future model review, but not a demonstrated repair for our borrowed methods. The current extracted maximum-state update already uses explicit comparison. |

Related nested-borrow work remains open according to the live GitHub API on
the review date:

- [#1189](https://github.com/AeneasVerif/aeneas/pull/1189), nested shared borrows
  used in loops: unmerged.
- [#1190](https://github.com/AeneasVerif/aeneas/pull/1190), nested-reference
  fixes: unmerged draft.
- [#1252](https://github.com/AeneasVerif/aeneas/issues/1252), distinct lifetimes
  in `Option<&T>::as_ref`: open. Its reported projection-lookup assertion is
  different from our enum-reader `lookup_loan` failure.
- [#1192](https://github.com/AeneasVerif/aeneas/issues/1192), successive loops
  over zipped mutable slice iterators: open despite the partial fix in #1331.

These statuses do not prove that our examples still fail on the candidates.
Fresh extraction is required to distinguish a fix from a related change.
The existing [CoW reproducer](reproducers/cow_regions/README.md) remains the
reference for the eight failing enum readers and four successful controls.

The MaxMap wrapper obstacle already has a validated local workaround:
explicit Option matches and namespace-safe local names allow `get_mut_with`,
`get_cow_with`, and `get_cow_with_value` to extract and compile on the working
pin. Its remaining wrapper contracts and concrete VecMap composition are
proof obligations; they should not all be attributed to the borrowed-CoW
extraction failure. See the [current checkpoint](PROGRESSIVE_LIST_PROOFS.md).

## Compatibility checks actually run

Both candidates' bundled Lean libraries were tested in isolated directories,
using Lean 4.31.0 and the project's already-built shared dependencies. Their
dependency pins match the project manifest. The production Aeneas and Tree
build paths were excluded from each candidate's `LEAN_PATH`; copied project
sources were not edited.

| Check | Working pin | `7ebd01d` | `505b6ca` |
| --- | --- | --- | --- |
| `Result` constructor case split and bind reduction below | Pass | Pass | Fail |
| Actual `Tree/TypesExternal` and `Tree/Types` | Existing validated build | Pass | Pass |
| Actual `Tree/Ssz/Models` | Existing validated build | Fail | Fail |
| Actual `Tree/Arbitrary/Models` | Existing validated build | Not run | Fail |
| Actual `Tree/Ssz/DecodeModels`, `Tree/Formatting/Models`, `Tree/Cow/EntryModels` | Existing validated build | Not run | Pass |
| Full proof library and axiom audit | Existing validated build | Not run | Not run |
| Fresh Rust extraction with matched Charon | Existing recorded probes | Blocked on toolchain installation | Blocked on toolchain installation |

The small `Result` compatibility probe is:

```lean
import Aeneas
open Aeneas Aeneas.Std Result

example {T : Type} (r : Result T) :
    (∃ value, r = ok value) ∨ (∃ error, r = fail error) ∨ r = div := by
  cases r with
  | ok value => exact Or.inl ⟨value, rfl⟩
  | fail error => exact Or.inr (Or.inl ⟨error, rfl⟩)
  | div => exact Or.inr (Or.inr rfl)

example {T U : Type} (value : T) (next : T → Result U) :
    (do let item ← ok value; next item) = next value := by rfl
```

[Commit df7059b9 (#1180)](https://github.com/AeneasVerif/aeneas/commit/df7059b918e91cd1ac37c6814f642a935948025e),
merged September 8, changes `Result` to use interaction trees. On the latest
release the case split expects `ret` and `vis`, and the second example no
longer closes by definitional reduction. Existing proof techniques therefore
need migration. `7ebd01d` is the immediate parent of that change and preserves
these two techniques; this is not a full compatibility claim.

[Commit 4f578dc (#1256)](https://github.com/AeneasVerif/aeneas/commit/4f578dc09aba9170bb7739ba2afd13ca02e867fa)
changes `Slice` from a list subtype to a structure with length, `ListN`, and
a bound proof. Both candidates reject our two-field constructor in
`Tree/Ssz/Models.lean:26`; latest also rejects the constructor in
`Tree/Arbitrary/Models.lean:16`. Upstream provides `Slice.from`, but porting
these definitions and their dependent proofs has not been attempted. The
older candidate therefore still requires a model/proof migration.

Review artifacts and individual compiler logs are under
`/tmp/milhouse-aeneas-upstream-j6mrhx0i/` in this session. In particular:
`Compatibility.lean`, `pinned-compatibility.log`,
`pre-itree-compatibility.log`, `latest-compatibility.log`,
`pre-itree-Tree-Ssz-Models.log`, `latest-Tree-Ssz-Models.log`, and
`latest-Tree-Arbitrary-Models.log`. These temporary artifacts are not a
replacement for the committed source audit reports.

## Next evaluation step

The candidates' Charon binaries require `nightly-2026-08-18`, which is not
installed. The attempt to install it failed because the session sandbox
denies writes to `~/.rustup/tmp`. Installation must happen outside this
session, or after restarting with the required sandbox access:

```sh
rustup toolchain install nightly-2026-08-18 --profile minimal \
  --component rustc-dev,rust-src,llvm-tools
```

Then, in isolated output directories:

1. Regenerate LLBC with each candidate's matched Charon and Rust toolchain;
   do not feed old LLBC to the new version or bypass version checks.
2. Run the CoW enum-reader/control reproducer, followed by actual `deref`,
   `make_mut`, and `next_cow` roots. Successful controls alone do not establish
   those methods, and partial output with admissions is not accepted.
3. Retest the original MaxMap borrowed-Option path and VecMap insertion,
   including the iterator filtering flag where relevant.
4. If a candidate resolves a required extraction gap, port the Slice models
   and dependent proofs in isolation. Latest additionally needs the Result
   migration. Regenerate and review all affected external templates and
   source models, then run the full build, axiom/import audit, model audit,
   all nine source suites, and relevant Rust tests before adopting a pin.

`7ebd01d` is a useful first comparison because it contains the September 3
fixes without the Result migration. It is not yet a validated upgrade.
Debug and Serde remain excluded; TreeHash remains deferred.
