# Aeneas upgrade review — 2026-09-10 (updated 2026-09-11)

**Current status: the September 7 trial cannot yet pass every existing check.**
With Miri and rustfmt now installed, production extraction, the complete
library audit (447 modules, 6,210 theorem declarations), the model audit, and
324 Rust tests pass. Eight source suites validate 51 proofs. The remaining
`usize::pow` comparison fails because Aeneas cannot translate the new
`overflow_checks<bool>` operation. The Core power proof also has three new,
explicit numeric-helper model boundaries. The working compiler is retained;
the trial has not been merged. The final full-MIR checkpoint below supersedes
the earlier missing-component and optimized-sysroot diagnostics.

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
`Tree/Arbitrary/Models.lean:16`. Upstream provides `Slice.from`. At this initial
stage, porting these definitions and their dependent proofs had not been
attempted. The follow-up
below records the completed main-library migration and remaining source-suite
failures.

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

The initial checkpoint (`dbbcb64`) compiled only 52 modules, with 7 failures
and 387 dependent modules blocked. Subsequent repairs migrated Vec, Slice,
and Array constructions and extensionality, clone and iterator reasoning,
mutable indexing, integer minimum, and SSZ encoding/roundtrip proofs.

At trial commit `5322d74`, the following checks passed:

| Check | Result |
| --- | --- |
| Fresh production extraction with the original Cargo lock | Pass; no admitted generated bodies |
| Direct compilation of every project module | 446 passed, zero failures or blocked imports |
| Full Lake build | Pass, 2,168 build jobs |
| Axiom/import audit | Pass, 6,210 theorem declarations across 446 modules |
| Model dependency audit | Pass, 42 roots and 151 local model declarations |
| Rust library tests with the arbitrary feature on the new nightly | 324 passed, zero failures |

The axiom audit's only nonstandard theorem dependency remains the existing
`triomphe.arc.Arc.ptr_eq_spec` (119 declarations). The declared external
axioms remain `core.mem.size_of.usize_spec` and `triomphe.arc.Arc.ptr_eq_spec`.
No new axioms or admissions were needed for that successful library build.
These results supersede the initial 52/7/387 compilation checkpoint.

The standalone source comparisons did not all validate. The full runners
stop because the installed nightly lacks rustfmt. Exploratory extraction
and Lean checks continued separately and do not count as complete audit
reports. Their results are:

| Source comparison | Result |
| --- | --- |
| FixedBytes | All five proofs compile on freshly extracted source, with the existing axiom expectations, after the equality proof repair in `730ae18`. |
| Option | The comparison file compiles using an experimental local model for the compiler-inserted `assume` intrinsic and an `Option<Infallible>` discriminant instance. Its existing axiom-free gate fails; the allowlist was not relaxed. |
| Core `u128::saturating_mul` | Aeneas fails with `Unimplemented binary operation` in the checked-multiplication path. |
| Core `u128::checked_pow` | Aeneas rejects a transmute from `u128` to `Option<NonZero<u128>>` in the new power-of-two optimization path. |
| Arbitrary | The provenance checker rejects a changed `size_hint` declaration after excluding an unused method. The cause was not investigated before halting. |

The two Core extraction failures prevent validating the existing direct
source proofs with this candidate. Aeneas exits with status 1 and generates
partial output; that output is not accepted or imported into the library.
These are compiler limitations, not discovered bugs in milhouse's Rust code.
The remaining source suites and borrowed-CoW controls were not rerun on the
candidate. Installing rustfmt alone would not resolve these extraction
failures.

The successful main-library audit predates the experimental `Tree.Intrinsics`
addition. It must not be presented as an audit of the later trial tip.
The unfinished source-validator adaptations and local intrinsic experiment
are preserved in trial commit `9309531`, with their limitations in
`aeneas-lean/SEPT7_TRIAL_STATUS.md` on `sept7-compiler-trial`. The trial branch
is not merged into the working branch.

Evidence is retained under `/tmp/milhouse-aeneas-upstream-j6mrhx0i/`:

- `sept7-build.log`, `sept7-build/report.json`, and `sept7-build/logs/`:
  successful direct dependency build.
- `sept7-full-axiom-audit.log`, `sept7-model-dependency-audit.log`, and
  `sept7-native-tests.log`: successful main-library audits and Rust tests.
- `core-extraction-probe/aeneas.log`: the two Core extraction failures.
- `option-extraction-probe/CheckModels.log` and
  `fixed-bytes-extraction-probe/CheckModels.log`: exploratory Lean results.
- `build_sept7.py`, `sept7-build-config.json`, `extract_probe.py`, and
  `compile_probe.py`: temporary diagnostic invocations, not adopted tooling.

The working Aeneas checkout remains clean at `b59d5188c082`, and its Charon
checkout remains clean at `cb50ff16b9f1`. The upgrade attempt is halted as
requested. No trial Rust, proof, compiler-pin, or audit-gate changes are
applied to the working branch. The existing proof goal remains incomplete;
no additional borrowed-CoW obligation was discharged by this trial.

## Resumed check: definitive full-MIR checkpoint

The resumed goal requests the compiler upgrade and repairs to all existing
proofs. The migration is preserved on `sept7-compiler-trial`, through proof
commit `f88baf5`, without changing the working compiler or Aeneas sources.

Miri and rustfmt are now installed for `nightly-2026-08-18`.
`cargo miri setup --print-sysroot` succeeds and returns
`/home/michael/.cache/miri`. The complete extraction/audit runners reject
Charon's optimized-sysroot fallback. The final checks use full MIR.

Commit `e9e7882` pins and installs the checksum-verified official bundle in
the trial's own ignored project cache. Lake, production extraction, and all
source-audit defaults use that bundle. Installation and repeat `--check`
pass. The original ignored Cargo lock remains byte-identical to the working
branch's lock. Full-MIR production extraction succeeds without changing the
trial's generated library files.

| Final check | Result |
| --- | --- |
| Full Lake build and axiom/import audit | Pass: 447 project modules and 6,210 theorem declarations |
| Model dependency audit | Pass: 42 roots, 151 local declarations |
| Native Rust library tests, arbitrary feature enabled | Pass: 324 tests |
| Option | Pass: 12 proofs, all axiom-free |
| Core | Pass: 7 proofs, 4 axiom-free; checked power has the boundaries described below |
| FixedBytes | Pass: 5 proofs |
| Tuple | Pass: 4 proofs |
| Vec | Pass: 3 proofs |
| SSZ offset | Pass: 4 proofs |
| Arbitrary | Pass: 3 proofs |
| VecMap | Pass: 13 proofs |
| Pow | Fail: Aeneas rejects `overflow_checks<bool>` before the comparison can compile |
| Existing CoW controls | Pass: 4 freshly extracted proofs, all axiom-free, plus native tests |
| Shared source-validator tests | Pass: 14 tests |

All eight successful source reports have current input hashes. The failed
Pow runner removes its previous success report and rejects partial output.
No theorem axiom allowlist has been relaxed. The two declared external axioms
remain `core.mem.size_of.usize_spec` and `triomphe.arc.Arc.ptr_eq_spec`;
the only nonstandard theorem dependency remains the Arc pointer contract
(119 declarations). The obsolete intrinsic experiment was removed in
`9642694`; the additional module is now `Tree.CompilerModels`, not
`Tree.Intrinsics`.

The Core checked-power proof follows both extracted squaring-loop forms and
the new power-of-two shortcut. It quantifies independently over the compiler
selector's base/exponent outcomes. Three new helpers (`ilog2`, `checked_shl`,
and `is_power_of_two`) are concrete mathematical foundation models whose
Rust implementations are not validated by that comparison. The report and
trial's Core README record these boundaries explicitly. This is a narrower
source-fidelity claim than saying all new numeric dependencies are extracted
and proved. The compiler's selector is also an explicit boundary; adding its
section parameter preserves every generated function body byte for byte.

The remaining power failure occurs at Rust `uint_macros.rs:3635`.
The new `usize::pow` selects `strict_pow` or `wrapping_pow` according to the
caller's overflow-check configuration. The normal full-MIR run and an
isolated `--monomorphize --rustc-arg=-Coverflow-checks=yes` probe both fail on
that operation. No supported setting found in the pinned compiler resolves
it. Replacing the LLBC operation with a constant or proving only one helper
would change the validation boundary; neither workaround has been applied.
See [issue 29](UPSTREAM_BUGS.md#29-september-aeneas-cannot-translate-the-overflow-check-selector-in-usizepow).

The candidate is therefore **not adopted**. The successful repairs remain on
the trial branch. Further work on Pow requires discussion of an upstream fix
or an explicit change to its modeling boundary. This is an Aeneas limitation,
not a discovered bug in milhouse Rust. Debug and Serde remain outside the
proof goal; TreeHash remains deferred. No new borrowed-CoW obligation has
been discharged.

Final session evidence is under `/tmp/milhouse-aeneas-upstream-j6mrhx0i/`:
`sept7-full-mir-production.log`, `sept7-final-source-*.log`,
`sept7-final-axiom-audit.log`, `sept7-final-model-audit.log`,
`sept7-final-native-tests.log`, and `sept7-final-cow-controls/`.
Detailed reports remain in the trial's ignored `aeneas-lean/.lake/` audit
directories. `pow-mono-probe/` preserves the unsuccessful flag probe.

### Branch follow-up

Fresh diagnostic callers on the same pinned compiler establish that the
strict branch has an additional extraction failure: `strict_pow` reports
`Unexpected result: Cps.Unit` at `Interp.ml:593`. Including its checked-power
body and panic helper does not resolve that caller failure. The panic helper
itself translates to `fail panic`. Resolving only the outer overflow selector
would therefore still leave an untranslatable source body.

The wrapping branch extracts with external numeric-helper templates but
cannot replace the existing checked-power proof because its overflow behavior
differs. The original Pow audit was rerun and still fails on
`overflow_checks<bool>`. The trial now preserves a two-function diagnostic
fixture and reproduction commands; [issue 29](UPSTREAM_BUGS.md#29-september-aeneas-cannot-translate-the-overflow-check-selector-in-usizepow)
records the exact results. No proof obligation was removed or weakened, and
the compiler remains unadopted. Completing the upgrade is still blocked on
an upstream repair or discussion of a change to the modeling boundary.
