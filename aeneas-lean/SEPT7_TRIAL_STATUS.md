# September 7 trial — halted, not adopted

The working `aeneas` branch retains Aeneas `b59d5188c082` and Charon
`cb50ff16b9f1`. This separate `sept7-compiler-trial` branch contains an
unfinished migration to Aeneas `7ebd01d19455`, Charon `85bba1f2a64d`, and Rust
`nightly-2026-08-18`. Aeneas sources and production Rust were not patched.

At commit `5322d74`, fresh locked production extraction, all 446 project
modules, the full Lake build, and the axiom/import audit passed. The audit
checked 6,210 theorem declarations; the only nonstandard theorem dependency
was the existing `triomphe.arc.Arc.ptr_eq_spec`. The model audit passed with
42 roots and 151 local declarations. All 324 Rust library tests passed.

The subsequent source-suite work is incomplete:

- The five FixedBytes comparison proofs pass on freshly extracted source
  with their existing axiom expectations (`730ae18`).
- The Option comparison file compiles with an experimental local `assume`
  model and a narrow `Option<Infallible>` discriminant instance, but fails its
  existing axiom-free expectations. Its allowlist has not been weakened.
- Core source extraction fails in `u128::saturating_mul` with “Unimplemented
  binary operation” and in `u128::checked_pow` with an unsupported transmute
  from `u128` to `Option<NonZero<u128>>`. Partial generated output is not
  accepted as proof evidence.
- The Arbitrary probe rejects a changed `size_hint` source declaration
  after exclusion. The cause has not been investigated.
- The new nightly lacks rustfmt. The complete source-suite runners therefore
  have not passed; manual extraction/Lean probes are not complete audits.

The later `Tree.Intrinsics` addition and source-validator edits are
experimental and are not covered by the successful 446-module audit above.
No compiler upgrade is approved by these results. The trial was halted under
the user's instruction to retain the current compiler if all existing proofs
could not be validated.

Session artifacts are in `/tmp/milhouse-aeneas-upstream-j6mrhx0i/`:
`sept7-locked-main-extraction.log`, `sept7-build/`,
`sept7-full-axiom-audit.log`, `sept7-model-dependency-audit.log`,
`sept7-native-tests.log`, and the `*-extraction-probe/` directories. The
temporary `extract_probe.py` and `compile_probe.py` helpers deliberately do
not write canonical source-audit reports. They are diagnostics only.
