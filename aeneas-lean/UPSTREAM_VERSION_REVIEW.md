# Aeneas upgrade review — 2026-09-10

**Decision after the follow-up trial: retain the working compiler.** The
September 7 candidate generates the existing extraction successfully, but
the full proof library does not pass after initial compatibility adaptations.
The user requested a halt if the existing proofs could not all be made to
pass; the upgrade attempt is stopped. Details are in the follow-up below.

Upstream contains relevant fixes, but none has yet been verified against our
exact borrowed-CoW failures. The latest release also breaks existing Lean
proof patterns. No changes from the isolated compiler trial are applied to the
working branch's Rust, extracted definitions, proofs, tool pins, audit version
gates, or Aeneas sources.

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

## Initial compatibility checks

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

## Original evaluation plan

At the initial review, the candidates' required `nightly-2026-08-18` was not
installed. Installation failed because the session sandbox denies writes to
`~/.rustup/tmp`. The user subsequently installed it outside the session using:

```sh
rustup toolchain install nightly-2026-08-18 --profile minimal \
  --component rustc-dev,rust-src,llvm-tools
```

The planned checks were the following. The user's subsequent instruction
prioritized existing proof compatibility and required halting on failure;
this plan is not authorization to continue after the failed trial.

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

## Follow-up: September 7 compiler trial stopped

After the toolchain installation, the user requested testing `7ebd01d` against
all existing proofs and halting if that did not succeed. The isolated worktree
is `/tmp/milhouse-aeneas-upstream-j6mrhx0i/milhouse-sept7`, on branch
`sept7-compiler-trial`, based on working-branch commit `872f21e`.

The verified tool versions are Aeneas `nightly-2026.09.08-7ebd01d`, Charon
`0.1.251 (85bba1f2a64ded1704586cdc26dfb62aeb4b7168)`, Rust nightly
`2026-08-18` at `8fa1c96cfd489e4c27654c144ae871ce2c4db6c6`, and Lean 4.31.0.

Fresh Charon and Aeneas extraction using the existing selected roots succeeds
with exit status zero. The original, ignored `Cargo.lock` was copied into the
worktree before the definitive run and verified byte-identical afterward.
The preliminary run without that lock resolved newer dependencies and is not
used as evidence for the compiler-only comparison. The definitive log is
`sept7-locked-main-extraction.log` in the review artifact directory.
Generated `Types.lean` and `Funs.lean` contain no `sorry` or `admit` bodies and
compile against the candidate after the initial local model adaptations.

The attempt ported byte-vector construction, arbitrary control-byte slices,
vector-pop construction, and initial UTF-8, arbitrary-generation, and SSZ
byte proofs to the new representations. These modules compile. In particular,
upstream `Vec` is now a structure wrapping a `Slice`; replacing every old Vec
constructor with `Slice.from` alone is insufficient. Array representation
changes also require explicit projection lemmas in byte proofs.

All 446 project modules were scheduled for direct Lean compilation in import
order, with a fresh output directory and candidate Aeneas library. Only shared
third-party dependencies were read from the working project's cache; its Tree
and old Aeneas output paths were excluded. The final attempt reports:

- 52 modules compiled successfully.
- 7 modules failed to compile.
- 387 modules were not checked because their imports depend on failed modules.

| Failed module | Remaining incompatibility |
| --- | --- |
| `Tree.Iterator` | The old vector subtype destructuring no longer applies; the attempted replacement still leaves the dependent iterator match unreduced. |
| `Tree.Ssz.ReadOffset` | Array reconstruction no longer reduces definitionally; the proof also applies `Subtype.ext` to the new Array structure. |
| `Tree.Arbitrary.Reflection` | The empty vector's list projection no longer reduces as the existing proof expects. |
| `Tree.PackedLeaf.Insert` | The generated generic vector mutable-index call no longer matches the specialized mutable-index expression by definitional equality. |
| `Tree.Ssz.FixedCursor` | Changed `Ord::min` reduction and Slice representation invalidate the existing reduction and subtype-extensionality steps. |
| `Tree.Vec.Clone` | The changed vector clone representation invalidates the existing result-injectivity step. |
| `Tree.Invariants` | Existing clone-length arguments and vector constructions depend on the old Vec/Slice representation. |

The full axiom/import audit, model audit, and nine standalone source suites
were not run on the candidate because the main proof compilation failed.
No claim is made that the uncompiled modules would pass, or that these are
the only remaining migration changes. This is a failed compatibility attempt,
not evidence that the underlying correctness statements are false.

Successful initial adaptations and extraction are preserved only in trial
commit `dbbcb64`; the unsuccessful iterator adaptation remains an uncommitted
experiment in that worktree. They are not merged into the working branch.
The complete attempt's logs and dependency report are `sept7-build.log` and
`sept7-build/report.json`; individual diagnostics are in `sept7-build/logs/`.
`build_sept7.py` and `sept7-build-config.json` retain the isolated compiler
invocations. All these artifacts are under the review directory above.

The working Aeneas checkout remains clean at `b59d5188c082`, and its Charon
checkout remains clean at `cb50ff16b9f1`. The upgrade attempt is halted as
requested. The existing proof goal remains incomplete; no additional
borrowed-CoW obligation was discharged by this trial.
