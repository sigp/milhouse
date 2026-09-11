# September 7 compiler adoption checkpoint

The September 7 candidate is adopted on the working `aeneas` branch in merge
commit `130ca10`. The former trial's compiler pin, setup helper, generated
code, proof repairs, and audit changes are integrated. Final checks ran in
`/home/michael/Programming/milhouse` using the project's default compiler
paths, not the trial worktree or an override to the old adjacent checkout.

## Compiler and approved assumption

`aeneas-toolchain.json` pins Aeneas `7ebd01d19455` (official release
`nightly-2026.09.08-7ebd01d`), Charon `85bba1f2a64d` (`0.1.251`), Rust
`nightly-2026-08-18`, and Lean 4.31.0. The checksum-verified bundle is
installed at `aeneas-lean/.lake/aeneas`; Lake, extraction, and source audits
use it by default. Installation and repeat verification both pass.
Miri and rustfmt are installed; extraction uses the full-MIR sysroot and
rejects the optimized fallback.

On 2026-09-11 the user approved **assuming `usize::pow` correct for now**.
`SOURCE_MODEL_ASSUMPTIONS.json` records the exact boundary. Its concrete Lean
model is retained: compute the natural-number power, return a machine word
when representable, and otherwise fail with `integerOverflow`. Correspondence
to Rust in the overflow-checking build, including its failure abstraction,
is trusted. No new Lean axiom is introduced. The model audit reports this
assumption, policy/model hashes, and ten conservative dependent API roots.

The former `core_pow_agrees` source comparison is deferred and is not counted
as proved. Its old proof and diagnostic command are preserved. The compiler
failures (`overflow_checks<bool>` and `strict_pow`'s `Cps.Unit`) remain recorded
in [issue 29](UPSTREAM_BUGS.md#29-september-aeneas-cannot-translate-the-overflow-check-selector-in-usizepow).
The old working-pin success report was archived rather than left looking
current. This is the only excluded existing proof check in the upgrade.

## Validation on the adopted working branch

| Check | Result |
| --- | --- |
| Full-MIR production extraction | Pass; regenerated files match the merge commit |
| Full Lake build | Pass: 2,169 jobs |
| Axiom/import audit | Pass: 447 project modules, 6,210 theorem declarations |
| Model dependency audit | Pass: 42 roots, 151 local declarations, explicit Pow assumption |
| Option source suite | Pass: 12 proofs |
| Core source suite | Pass: 7 proofs |
| FixedBytes source suite | Pass: 5 proofs |
| Tuple source suite | Pass: 4 proofs |
| Vec source suite | Pass: 3 proofs |
| SSZ offset source suite | Pass: 4 proofs |
| Arbitrary source suite | Pass: 3 proofs |
| VecMap source suite | Pass: 13 proofs |
| Fresh CoW controls | Pass: 4 proofs without axioms, plus native test and formatting |
| Rust library tests, arbitrary feature enabled | Pass: 324 tests |
| Native power tests with overflow checks explicitly enabled | Pass: 4 tests; these do not replace the deferred Lean comparison |
| Python source-validator tests | Pass: 17 tests |

The eight required source suites validate 51 proofs: 20 axiom-free and 31
using only the permitted standard Lean axioms. Every source report's input
hashes match the adopted files. Axiom allowlists are unchanged. The only
nonstandard theorem dependency remains the existing Arc pointer contract
(119 declarations); declared external axioms remain
`core.mem.size_of.usize_spec` and `triomphe.arc.Arc.ptr_eq_spec`.

The Core checked-power comparison retains explicit numeric-helper foundations
for `ilog2`, `checked_shl`, and `is_power_of_two`, plus a universally quantified
compiler selector. Its exact boundaries are documented in the
[Core README](reproducers/core_models/README.md) and source report. These
helper implementations are not claimed as independently source-validated.

The original ignored Cargo lockfile is byte-identical after all checks:
`87da418b718a271fd77db47e21930d2e8608f517c4a234e5e7b81f2d37d01f42`.
Production Rust is unchanged by the migration. The adjacent Aeneas and Charon
source checkouts remain clean at their original revisions; no compiler source
was patched. Debug and Serde remain out of scope, and TreeHash remains
deferred. The compiler upgrade does not discharge new borrowed-CoW obligations
or complete the broader ProgressiveList proof goal.

## Reproduce and inspect

Follow [the verification guide](README.md) for setup and required commands.
Final command logs and the run manifest are under
`aeneas-lean/.lake/sept7-upgrade/`. The detailed axiom, model, and eight source
reports are in their respective `.lake/*-audit/` directories. The CoW report,
freshly extracted bodies, and four axiom-free proofs are under
`.lake/sept7-upgrade/cow-controls/`.

The earlier trial evidence and unsuccessful power probes remain in
`/tmp/milhouse-aeneas-upstream-j6mrhx0i/`. See
[the version review](UPSTREAM_VERSION_REVIEW.md) for the investigation history
and the user-approved change that removed the adoption blocker.
