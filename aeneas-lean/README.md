# Lean verification

The project uses the September 7 Aeneas candidate with the compatibility
repairs recorded in [the migration checkpoint](SEPT7_TRIAL_STATUS.md).
The user approved temporarily trusting `usize::pow` on 2026-09-11; its Rust
source comparison is deferred. All other existing proof checks remain required.

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

Run the eight required source-comparison suites separately:

```sh
(
  set -e
  for suite in option core fixed-bytes tuple vec ssz-offset arbitrary vec-map; do
    python3 "scripts/aeneas-audit-$suite-models.py"
  done
)
```

Each successful runner writes a report under `aeneas-lean/.lake`, including
tool versions, input hashes, source provenance, and per-proof axiom
dependencies. Failed extraction, incomplete bodies, and unexpected axioms
do not produce a success report. Reproducer READMEs describe the individual
comparison boundaries; earlier recorded results retain their original pins.

`usize::pow` keeps its concrete mathematical model: return the natural-number
power when it fits in a machine word, otherwise fail with `integerOverflow`.
Its agreement with Rust, including the failure abstraction, is assumed under
the approved [source-model policy](SOURCE_MODEL_ASSUMPTIONS.json). No new Lean
axiom is introduced. The model audit reports this assumption and the API roots
that conservatively depend on it. The required source suites prove 51 lemmas;
the former `core_pow_agrees` comparison is not counted as proved.

`python3 scripts/aeneas-audit-pow-models.py` remains an optional diagnostic.
It is expected to fail on the candidate's unsupported power operations and
is excluded from the required checks. The old comparison and branch probes
remain available for removing this temporary assumption later.

Debug and Serde implementations remain outside the proof goal. TreeHash
implementations remain deferred. See the [proof scope](PROGRESSIVE_LIST_PROOFS.md#goal-and-scope)
for the included APIs and retained historical results.
