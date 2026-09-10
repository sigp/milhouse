# September 7 trial — active, not yet adopted

The active goal is to update Aeneas to the September 7 candidate and repair
all existing proofs. Work resumed after the earlier halted checkpoint.
The working `aeneas` branch still retains Aeneas `b59d5188c082` and Charon
`cb50ff16b9f1`; migration work is isolated on `sept7-compiler-trial`.
Aeneas sources and production Rust have not been patched.

## Compiler setup and library validation

Commit `e9e7882` pins the official September 7 release in
`aeneas-toolchain.json`. The checksum-verified bundle is installed under
`aeneas-lean/.lake/aeneas`, and the trial's Lake configuration, extraction
script, and source-audit defaults use it. See [setup instructions](README.md).
The setup script's installation and repeat `--check` both pass.

With this installed bundle, the full Lake build and axiom/import audit pass:
447 project modules and 6,211 theorem declarations. This includes the
experimental `Tree.Intrinsics` module. The only nonstandard theorem
dependency is the existing `triomphe.arc.Arc.ptr_eq_spec` (119 declarations).
The declared external axioms remain `core.mem.size_of.usize_spec` and
`triomphe.arc.Arc.ptr_eq_spec`. The model audit passes with 42 roots and
151 local declarations.

Earlier commit `5322d74` passed fresh locked production extraction and all
446 then-existing modules. All 324 Rust library tests passed on the new
nightly. The definitive extraction used the original ignored `Cargo.lock`.
Production extraction must be repeated with the full-MIR sysroot described
below before the upgrade can be adopted.

## Source comparisons and outstanding environment requirement

The installed nightly is missing **Miri and rustfmt**. Charon's diagnostic
logs confirm that it fell back to Rust's optimized standard library. This
can inline low-level operations across Aeneas's model boundaries. The exact
pinned Charon source also lists Miri as a required toolchain component.
The previous extraction failures therefore do not establish failure with
the intended full-MIR sysroot; retesting is required.

The user has been asked to run outside the session:

```sh
rustup component add --toolchain nightly-2026-08-18 miri rustfmt
```

The existing session sandbox prevents Rust component installation. The
source runner now checks both components and rejects Charon's fallback
warning. The production extraction script checks Miri before extraction and
also rejects fallback. Its current preflight stops before regenerating
production files, as expected.

Exploratory comparisons already completed are:

- FixedBytes: all five proofs pass with existing axiom expectations
  (`730ae18`).
- Tuple: all four proofs pass unchanged.
- Arbitrary: all three proofs pass with existing axiom expectations
  (`48f74aa`). The provenance mismatch was exclusively fresh statement and
  block numbering; the checker now validates separate bijections and then
  compares complete declarations (`5a01112`). Twelve checker tests pass.
- Option: eleven proofs retain their axiom-free status (`93fe26e`). The
  residual comparison compiles with a local intrinsic experiment but fails
  its existing axiom-free gate. The allowlist has not been relaxed; retest
  the source using full MIR before deciding which model is needed.
- CoW controls: all four separately extracted control proofs pass without
  axioms; native control tests also pass. This establishes no new borrowed
  CoW support beyond those existing controls.

On the optimized fallback, Core extraction fails on checked multiplication
and a `NonZero` transmute, Vec extraction fails inside inlined allocation
operations, SSZ extraction fails on a pointer-metadata projection, and
VecMap's extracted `Option::as_mut` cannot copy a mutable borrow. The Pow
source body has also changed. These suites must be re-extracted using the
proper sysroot; partial output is not accepted as proof evidence. None of
the nine complete source-suite runners has passed on the candidate yet.

## Remaining work

After the components are installed, regenerate production and source-suite
extractions with the intended full-MIR sysroot, repair remaining comparisons,
and run all nine complete source suites. Repeat affected library audits,
verify the scope and source/model boundaries, and integrate the compiler pin
and proof repairs into the working branch only after those checks pass.
Debug and Serde remain excluded; TreeHash remains deferred.

## Evidence

Session artifacts are in `/tmp/milhouse-aeneas-upstream-j6mrhx0i/`:

- `sept7-bundle-axiom-audit.log` and `sept7-bundle-model-audit.log`: latest
  successful audits against the installed bundle.
- `sept7-locked-main-extraction.log`, `sept7-build/`, and
  `sept7-native-tests.log`: earlier extraction, library build, and Rust tests.
- `sept7-option-model-audit.log` and `sept7-full-mir-preflight.log`: verified
  missing-Miri preflight failures.
- `*-extraction-probe/`: exploratory source comparisons and diagnostics.
  `cow-control-extraction-probe/proofs.log` records all four control proofs.

The temporary `extract_probe.py` and `compile_probe.py` helpers do not write
canonical source-audit reports. The disposable `sept7-cargo-target` build
cache was removed to free 2.4 GB; source, commits, and validation logs remain.
