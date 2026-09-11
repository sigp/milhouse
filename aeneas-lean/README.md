# Lean verification

The September 7 compiler migration is preserved on this trial branch.
The Pow source comparison remains blocked by an unsupported Aeneas operation.
See [the trial status](SEPT7_TRIAL_STATUS.md) for the completed checks and
model boundaries. The working branch retains its existing compiler.

## Toolchain

The [compiler pin](../aeneas-toolchain.json) selects Aeneas `7ebd01d19455`,
Charon `85bba1f2a64d`, Rust `nightly-2026-08-18`, and Lean `4.31.0`.
Install the Rust components and the official Linux x86-64 compiler bundle
from the repository root:

```sh
rustup toolchain install nightly-2026-08-18 --profile minimal \
  --component rustc-dev,rust-src,llvm-tools,miri,rustfmt
python3 scripts/aeneas_toolchain.py
python3 scripts/aeneas_toolchain.py --check
```

The setup script requires Python 3.12 or newer. It verifies the release
archive's SHA-256 digest before extraction, checks both compiler versions
and the Lean backend version, and installs into `aeneas-lean/.lake/aeneas`.
It does not install Rust components or modify an adjacent Aeneas checkout.
Use `--archive /path/to/aeneas-linux-x86_64.tar.gz` for an existing download;
the same digest check applies.

Charon uses `cargo miri setup` to obtain standard-library bodies with full
MIR. A missing Miri component causes Charon to fall back to an optimized
sysroot, which changes the extracted bodies and can cross unsupported
operation boundaries. Both the main extraction script and source-audit
runner reject this fallback. Installing rustfmt is also required for the
source-audit formatting checks.

## Build and validate

Preserve the existing `Cargo.lock` while comparing compiler versions.
From the repository root:

```sh
bash scripts/aeneas-extract.sh
python3 scripts/aeneas-audit-axioms.py
python3 scripts/aeneas-audit-progressive-models.py
```

The axiom audit builds the whole library before checking its declarations
and imports. For a build without the audit, run `lake build` from
`aeneas-lean`. Explicit compiler paths remain supported through `CHARON` and
`AENEAS`; an alternate Lean backend uses
`lake build -Kaeneas=/path/to/aeneas/backends/lean`.

Run all nine source-comparison suites separately:

```sh
(
  set -e
  for suite in option core fixed-bytes tuple vec ssz-offset arbitrary pow vec-map; do
    python3 "scripts/aeneas-audit-$suite-models.py"
  done
)
```

Each successful runner writes a report under `aeneas-lean/.lake`, including
tool versions, input hashes, source provenance, and per-proof axiom
dependencies. Failed extraction, incomplete bodies, and unexpected axioms
do not produce a success report. Reproducer READMEs describe the individual
comparison boundaries; earlier recorded results retain their original pins.

Debug and Serde implementations remain outside the proof goal. TreeHash
implementations remain deferred. See the [proof scope](PROGRESSIVE_LIST_PROOFS.md#goal-and-scope)
for the included APIs and retained historical results.
