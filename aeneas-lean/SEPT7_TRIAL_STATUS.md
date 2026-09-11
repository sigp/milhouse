# September 7 trial — Pow source blocker; not adopted

The migration is preserved on `sept7-compiler-trial`, through proof commit
`f88baf5`. The working `aeneas` branch retains Aeneas `b59d5188c082` and
Charon `cb50ff16b9f1`. No production Rust or Aeneas/Charon source was patched.
The compiler upgrade is incomplete because one existing source comparison
cannot be extracted by the candidate.

## Validated checkpoint

Miri and rustfmt are installed for `nightly-2026-08-18`; Miri's full-MIR
sysroot is `/home/michael/.cache/miri`. The setup helper's installation and
repeat version/checksum check pass. See [setup instructions](README.md).
The audit runners reject fallback to the distributed optimized sysroot.

| Check | Final result |
| --- | --- |
| Production extraction with the original Cargo lock and full MIR | Pass; generated library files unchanged |
| Full Lake build and axiom/import audit | Pass: 447 project modules, 6,210 theorem declarations |
| Model dependency audit | Pass: 42 roots, 151 local declarations |
| Rust library tests on the new nightly, arbitrary enabled | Pass: 324 tests |
| Option source suite | Pass: 12 proofs, all axiom-free |
| Core source suite | Pass: 7 proofs, with the additional boundaries below |
| FixedBytes source suite | Pass: 5 proofs |
| Tuple source suite | Pass: 4 proofs |
| Vec source suite | Pass: 3 proofs |
| SSZ offset source suite | Pass: 4 proofs |
| Arbitrary source suite | Pass: 3 proofs |
| VecMap source suite | Pass: 13 proofs |
| Pow source suite | Fail during Aeneas extraction |
| Existing CoW controls | Pass: 4 fresh proofs without axioms, plus native tests and formatting |
| Shared source-validator tests | Pass: 14 tests |

All eight successful source-suite reports have current input hashes. Together
they validate 51 existing source/composition/invariant proofs. The failed Pow
suite writes no success report. The axiom allowlists remain unchanged.
The only nonstandard theorem dependency in the main library is the existing
Arc pointer contract (119 declarations). The two declared external axioms
remain `core.mem.size_of.usize_spec` and `triomphe.arc.Arc.ptr_eq_spec`.

The earlier `Tree.Intrinsics` experiment was removed after full-MIR Option
extraction succeeded without it (`9642694`). `Tree.CompilerModels` is the
additional module in this checkpoint and introduces no axiom declarations.

## Core comparison boundaries

The new Rust checked-power algorithm contains a power-of-two shortcut and
two squaring-loop forms, duplicated across the outer selector branches.
The proof validates all those branches for every base and exponent,
including zero, overflow, and termination. The compiler selector is
universally quantified, with independent base and exponent outcomes.
Its audited section parameter is the only generated Lean change; removing
it recovers the original bytes, and all function bodies are preserved.

Three new numeric helpers are explicit mathematical foundations:
`u128::ilog2`, `u128::checked_shl`, and `u128::is_power_of_two`. Their Rust
implementations are **not source-validated by this suite**. The checked-power
comparison is conditional on these models and existing scalar foundations.
See the [Core comparison](reproducers/core_models/README.md) for the exact
boundary and report fields. Passing the kernel axiom gate is not a proof
of the models' correspondence to Rust.

## Remaining failure and adoption decision

The new `usize::pow` body selects `strict_pow` or `wrapping_pow` using
`core::intrinsics::overflow_checks()`. September 7 Aeneas rejects the LLBC
operation `overflow_checks<bool>` at `uint_macros.rs:3635`. Charon and native
tests pass, but Aeneas exits 1 and emits partial files, which are rejected.
A separate `--monomorphize --rustc-arg=-Coverflow-checks=yes` extraction
reaches the same failure.

The working compiler is retained because the candidate cannot validate all
existing proofs. Further work requires discussion of an upstream fix or an
explicitly reviewed change to the source-model boundary. No LLBC operation
was replaced by a constant, and no Rust algorithm was substituted to bypass
the failure. See [issue 29](UPSTREAM_BUGS.md#29-september-aeneas-cannot-translate-the-overflow-check-selector-in-usizepow).

No bug in milhouse Rust was discovered. Debug and Serde implementations
remain out of scope, TreeHash remains deferred, and the control checks do
not discharge any new borrowed-CoW obligation.

## Evidence

Final session artifacts are under `/tmp/milhouse-aeneas-upstream-j6mrhx0i/`:

- `sept7-full-mir-production.log`: full-MIR production regeneration.
- `sept7-final-source-*.log`: all nine complete source runners.
- `sept7-final-axiom-audit.log` and `sept7-final-model-audit.log`: complete
  library and model audits at the final proof checkpoint.
- `sept7-final-native-tests.log`: all 324 Rust tests.
- `sept7-final-cow-controls/`: fresh control extraction, proofs, formatting,
  and native tests.
- `pow-mono-probe/`: unsupported operation with explicit compiler flags.

Detailed successful reports and generated source files remain under the
trial's ignored `aeneas-lean/.lake/*-model-audit/` directories. The candidate
pin and reproduction scripts are committed; temporary exploratory helpers
are not accepted as substitutes for the complete audit runners.
