# ProgressiveList model dependency audit

The current scope excludes Debug and Serde and defers TreeHash. Borrowed
`Cow::deref`, `Cow::make_mut`, and `ProgressiveListIterCow::next_cow` remain
required but unavailable in extraction. See the [goal and scope](PROGRESSIVE_LIST_PROOFS.md#goal-and-scope)
and [API inventory](PROGRESSIVE_LIST_API_AUDIT.md).

## Reproduce the dependency inventory

From the repository root, run:

```sh
python3 scripts/aeneas-audit-progressive-models.py
```

The command builds the library, then reads the elaborated environment using
`AuditProgressiveListModels.lean`. The 42 roots in
`PROGRESSIVE_LIST_MODEL_ROOTS.json` account for all 19 inherent methods, the
available included trait methods, read-only iterator methods, and consuming
`Cow::into_mut`. The PartialEq dictionary covers both `eq` and inherited `ne`;
concrete extraction callers select inherited Clone and Arbitrary methods.
Missing borrowed methods are not silently counted as covered roots.

The traversal follows constants in definition bodies and records referenced
project declarations. It includes types inside expressions, complete trait
dictionaries, and branches that might be unreachable for supplied arguments.
It records opaque boundaries and does not unfold theorem proofs or opaque
bodies. Generic callback fields remain abstract; their implementations are
governed by the operation's explicit hypotheses. Thus this is a conservative
definition-dependency inventory, not an execution call graph or a Rust
refinement proof. Aeneas/foundation definitions are traversed, but only local
`Tree` declarations are reported; this is not a complete foundation-model audit.

The driver checks the exact root-label inventory and inherent declarations,
root definitions from the generated `Tree.Funs`, complete output, unique
dependency records, known local model modules, and absence of selected
incompatible models. It rejects replacements of core milhouse implementations
by local external models, including references to the older
`List::intra_rebase` identity model, hash-map abstractions, shared lock writes,
and no-op external Debug formatters. A failed run removes any older report.
Logs, the raw inventory, and the report are in `.lake/model-audit/`.

## Current findings

The audit passes for 42 roots and 151 referenced local model declarations.
The count includes types, generated helpers, and referenced proof constants;
it is not a count of independent trusted operations.

| Local module | Referenced declarations | Boundary to review |
| --- | ---: | --- |
| `Tree.TypesExternal` | 22 | Value representations for Arc/locks, byte input, and entry footprints |
| `Tree.FunsExternal` | 70 | Numeric/option operations, vectors, fixed bytes, Arc/lock plumbing, and vector comparison |
| `Tree.Cow.EntryModels` | 4 | BTree and vec_map vacant insertion and mutable write-back footprints |
| `Tree.Ssz.Models` | 9 | Encoder state, offset writes, append/finalize order, logical growth checks |
| `Tree.Ssz.DecodeModels` | 8 | Four-byte offset reads and Rust error mapping |
| `Tree.Formatting.Models` | 27 | Default-option SSZ builder-error messages and string output |
| `Tree.Arbitrary.Models` | 11 | Pinned control-byte consumption, element generation, and trait defaults |

None of the 42 closures references `List::intra_rebase`, the hash-map/hasher
models, or SmallVec models. Their presence in the shared external file does
not make them dependencies of the included ProgressiveList entry points.
The hash-map abstraction's comments now state its restricted domain: erasing
hashing does not preserve arbitrary callback effects or failures. Model bodies
were unchanged in the initial inventory checkpoint `07ef38d`; the subsequent
tuple correction is described below.

The BTreeMap lookup model occurs conservatively under `apply_updates` through
`utils.opt_hash`. The actual progressive update source and generated body pass
`None` to binary rebuilding (`src/progressive_tree.rs`,
`ProgressiveTree.with_updated_leaves_recursive`). Binary recursive calls retain
that parameter, and the existing `Tree/BulkUpdate/Success.lean` proofs reduce
`utils.opt_hash none` directly. Thus these calls do not execute BTreeMap lookup
or its tuple-comparison dictionary. This conclusion uses the supplied argument
and branch proofs, beyond the unspecialized inventory alone. Similarly,
Arbitrary size-hint callers carry the full trait dictionary, so their closures
include generator definitions even though the default size-hint body returns
its fixed answer. Runtime reasoning still uses the existing branch proofs.

SSZ error formatting remains relevant to included decoder results even though
general Debug implementations are excluded. The specialized formatter's
string-buffer and default-option contract must not be extended to general
formatter options, user sinks, or lock observation without further work.

## Option source comparisons

Run `python3 scripts/aeneas-audit-option-models.py` from the repository root.
The [source comparison](reproducers/option_models/README.md) explicitly includes
the pinned standard-library Option bodies in Charon and extracts them into an
independent namespace. Eleven local models equal their entire generated bodies
for all inputs and callback dictionaries, including callback failure/divergence
and skipped branches. All eleven comparisons validate without axioms.

`Option<&T>::cloned` fails direct extraction on the locally bound regions of
the `T::clone` function item (UPSTREAM_BUGS issue 23). A twelfth axiom-free
theorem checks its source-level `map(T::clone)` composition using the fully
extracted `map` body and actual clone callback. Two native tests cover clone
count, nonidentity results, skipped calls, and panic propagation. The report
keeps direct extraction and composition evidence separate.

The check validates transparent standard-library LLBC provenance and fresh
generated output and rejects incomplete bodies and missing axiom reports.
Seven malformed inventory/report cases are rejected. Its generated modules
are outside `Tree` and have a separate compilation/axiom gate, so the main
library theorem count is unchanged. The comparisons retain Aeneas's reference
abstraction and omitted destructor execution; they are not a compiler or full
Rust refinement proof. Numeric/container and the other model boundaries still
need their remaining review. No production model or Aeneas source changed.

## Core source comparisons

Run `python3 scripts/aeneas-audit-core-models.py` from the repository root.
The [core source comparisons](reproducers/core_models/README.md) prove the local
`mem::take`, `usize::div_ceil`, `u128::saturating_mul`, and `u128::checked_pow` models equal fresh
extraction of their actual standard-library bodies. `take` matches for arbitrary Default results without
axioms. Ceiling division matches for every pair of machine-word inputs,
including zero divisors, using only standard Lean axioms and no arithmetic
bound or positivity premise. Its rounding bound is derived internally.
Saturation also matches for every input, including overflow, with only
standard Lean axioms and no size premise. Its called checked multiplication
remains an existing Aeneas foundation primitive.
Checked power matches for every `u128` base and `u32` exponent. The proof
derives loop termination, the accumulator invariant, and sound overflow
detection, without imposing an arithmetic or termination premise on callers.
It also uses only standard Lean axioms and the existing arithmetic foundation.

Seven native tests cover Default call order, movement without dropping the old
value, the tested default-panic state, ceiling-division word boundaries, and
zero divisors, plus 35 saturation boundary pairs, 77 checked-power reference
pairs, and eight large-exponent cases. Both this suite and the
Option suite pass with the shared
source/provenance checker and per-theorem axiom policy. Eleven malformed core
inventory/report inputs and an injected axiom in an Option proof are rejected.

The comparisons retain the Aeneas foundation/reference abstractions and omit
destructor execution. No production Rust, local model body, or Aeneas source
changed; the main library and dependency counts are unchanged. These results
reduce the remaining model review without completing borrowed CoW or the
other numeric/container boundaries.

The remaining numeric probe retains the now-verified checked-power and
saturation bodies as controls. Trailing-zero counting, next-power-of-two
rounding, and ordinary power still reach missing compiler intrinsics. Broader
source inclusion exposes unsupported overflow-pair operations inside existing
foundation primitives. The preserved callers, exact commands, and trust
boundary are in the core comparison README and UPSTREAM_BUGS issue 24.
Incomplete/template output is never imported as verified code.

## Fixed-byte cache source comparisons

Run `python3 scripts/aeneas-audit-fixed-bytes-models.py` from the repository root.
The [fixed-byte comparisons](reproducers/fixed_bytes_models/README.md) validate
all five reached `FixedBytes` models against fresh extraction of
`alloy-primitives` 1.0.0: clone, equality, the zero constant, default, and
`is_zero`. Each equality holds for all array lengths and byte contents,
including empty arrays, without additional premises. Clone is axiom-free;
the other four use only standard Lean axioms. The existing Aeneas array/byte
foundation is retained.

The shared runner now supports locked Cargo dependencies and verifies global
constant/initializer links as well as function provenance. The fixed-byte
audit, its four native tests, and the existing core and Option audits pass.
Eleven malformed source inventories and four malformed axiom reports are
rejected. The source, manifest, lockfile, and dependency source hashes are
recorded in the report. These results support included cache initialization
and rebasing; they do not change the scope exclusions or complete the goal.
No production/model/Aeneas changes were made, and the main library and
dependency counts are unchanged.

## Vector source comparisons

Run `python3 scripts/aeneas-audit-vec-models.py` from the repository root.
The [vector comparisons](reproducers/vec_models/README.md) validate
`Vec::is_empty`, vector `eq`, and vector `ne` against the pinned source bodies.
Equality matches the corrected local `milhouse_models.vec_eq`; inequality
matches the existing vector foundation model. Both permit arbitrary callback
results without consistency or termination assumptions, preserving length
shortcuts, actual element `ne` dispatch, failure, and divergence.

Aeneas's builtin matching otherwise suppresses the comparison source bodies.
The runner changes only their final name identifiers in temporary LLBC and
checks the entire restored file against the original, including bodies,
signatures, IDs, and call targets. Actual `RangeFull` source indexing is
included. Vector length/indexing and slice comparison remain foundation
boundaries; no Aeneas source or local model is changed.

At `1a575ec`, all three comparisons and six native tests pass. Nine malformed
source inventories, ten invalid name changes or extra LLBC mutations, and
four malformed or excessive axiom reports are rejected. All five source suites
pass with the shared runner: 27 direct comparisons and one Option cloned
composition, totaling 28 proofs (16 axiom-free, twelve standard-only).

Direct `pop` and owning-iterator `next_back` extraction still fails on container
field access; including the container types exposes a further type-analysis
failure. Their preserved native tests cover movement, capacity, mixed
iteration, exhaustion, zero-sized elements, and drops, but do not complete
source fidelity. See UPSTREAM_BUGS issue 25. These standalone checks leave the
main proof library and 42-root/151-declaration inventory unchanged.

## Tuple source comparisons

Run `python3 scripts/aeneas-audit-tuple-models.py` from the repository root.
The [tuple comparisons](reproducers/tuple_models/README.md) validate all four
local pair-comparison bodies against fresh extraction of pinned `core::tuple`
source: `eq`, `ne`, `partial_cmp`, and `cmp`. They permit arbitrary callback
results, preserve short-circuiting and failure/divergence, and need no
consistency or termination premise. Equality and inequality are axiom-free;
the ordering comparisons use only the existing models' `propext`.

Four native tests cover 59 callback-answer combinations and exact method/order
traces. Four unused newer `PartialOrd` defaults require unsupported function
pointers; the runner omits exactly those defaults and verifies identical
expanded source declarations for all four comparisons before and after the
exclusions. Complete generated modules and all four axiom reports are required.
This does not verify the broader `PartialOrd` interface or its other methods.

At `c948ef8`, all four source suites pass with the shared runner extension:
24 direct comparisons and the separate Option cloned composition, totaling
25 proofs (16 axiom-free, nine standard-only). Nine malformed inventories,
a changed body after exclusions, and four malformed or excessive axiom reports
are rejected. The main proof library and 42-root/151-declaration inventory are
unchanged; their gates were not repeated for these standalone checks. Remaining
model boundaries and borrowed CoW are still open; the goal is incomplete.

## Tuple inequality correction

Review of the referenced tuple dictionary found a local model defect: its
`ne` negated tuple `eq`, while the pinned Rust implementation calls element
`ne` with left-to-right short-circuiting. These calls need not have the same
effects, failure, or divergence behavior. Commit `c47faba` corrects the model
without imposing callback-coherence laws or changing Rust or Aeneas.

`Tree/Tuple/Comparison.lean` proves the first-true shortcut, exact second-call
delegation after a false first result, first-call failure/divergence propagation,
and necessary and sufficient conditions for both Boolean success results.
The six lemmas failed against the former model and pass after correction.
Four [native regression tests](reproducers/tuple_comparison/README.md) confirm
the Rust callback order, both second-call answers, and failure propagation.
The optional-hash branch evidence above limits the impact of this finding:
it does not show a defect in ProgressiveList's public update proofs.

Validation after `c47faba`: the full library builds (2,024 jobs), and the
axiom/import audit covers 4,965 theorem declarations across 308 modules.
All seven declarations in `Tree.Tuple.Comparison` (six named lemmas and the
generated equation theorem) use only standard Lean axioms or none. Across the
library, 4,903 declarations are standard-only and 62 additionally use the
existing Arc pointer contract. The model dependency gate still passes for all
42 roots and the same 151 local declarations. No new axiom or admission is
introduced. The focused Lean build, four native tests, and Rust formatting
check also pass.

## Trusted boundaries and remaining work

- Clone and dependent rebase read laws now require agreement after the actual
  backing fallback, without exact raw map-read equality. `LookupResultsAgree`
  compares raw `Result (Option T)` outcomes, preserving failure and divergence
  and permitting an absent entry to match a value supplied by the fallback.
  The public lookup equivalences prove this criterion exact at every machine
  index, without backing invariants or assumed lookup success. Combined with
  maximum extent, it is necessary and sufficient for represented sequence
  preservation; the new clone/clone_from success equivalences also include
  actual pending-map clone termination. All dependent rebase sequence/cache
  contracts use the weaker law, while pending-update observers retain their
  own emptiness laws. At checkpoint `b93748b` (lookup criteria `38c8b6d`), the
  focused and full builds pass (2,034 jobs), and the axiom/import audit validates
  5,099 declarations across 318 modules. New lookup and clone criteria use
  only standard Lean axioms. No Rust, extraction, external model, or Aeneas
  source changed; the 42-root/151-local-declaration dependency gate was not
  repeated for these proof-only changes. Concrete map-model fidelity remains
  a separate obligation.
- Append now requires the new pending value at the appended index and lookup
  agreement after the original backing fallback elsewhere. `AppendReadAgrees`
  describes these raw outcomes; its public-read equivalence handles failures
  and divergence and needs a backing bound only for the appended-key query.
  The boundary lemma proves raw-map/public-read equality outside backing, and
  an adapter derives the new contract from the old exact insertion law.
  `push_represents_append_iff` proves lookup agreement and exact maximum are
  jointly necessary and sufficient for the complete sequence postcondition
  after successful execution. The total append proof now uses this criterion;
  its theorem conclusions are unchanged. These proof-contract results do not
  verify concrete map fidelity or replace source models.
  At checkpoint `2e4927d` (lookup foundations `79bd2a6`), the focused and full
  builds pass (2,035 jobs), and the axiom/import audit validates 5,108
  declarations across 319 modules. All new and revised append results use
  only standard Lean axioms. No Rust, extraction, external model, or Aeneas
  source changed; the 42-root/151-local-declaration dependency gate was not
  repeated for these proof-only changes.
- Mutable and consuming CoW write-back now require lookup agreement after the
  original backing fallback, together with maximum-result agreement. The new
  generic map laws describe raw lookup outcomes and are implied by the retained
  exact insertion/lookup laws for any backing function. `WriteBack.lean` proves
  these lookup and maximum conditions jointly necessary and sufficient for
  in-bounds sequence replacement, and both public continuation equivalences
  specialize it to actual calls. Existing sequence and total contracts use the
  weaker laws. The read criteria retain failure/divergence without assuming
  lookup success or backing validity. Initial reads, clone execution, and the
  actual consuming CoW entry/metadata footprint are unchanged; the map's CoW
  write law still applies to `Written` footprints. At checkpoint `7d329d7`
  (foundations `a027551`, `ac16012`), focused and full builds pass (2,036 jobs),
  and the axiom/import audit validates 5,117 declarations across 320 modules.
  All new and revised write-back results use only standard Lean axioms. No
  Rust, extraction, external model, or Aeneas source changed; the dependency
  inventory remains 42 roots/151 local declarations and its gate was not
  repeated for these proof-only changes. Concrete map fidelity and borrowed
  CoW extraction remain separate obligations.
- The separate nonmutating rebase observer law now also drops exact maximum
  identity. `UpdateMap/Length/Equivalence.lean` proves a necessary-and-sufficient
  relation on the raw maximum-query results, including mathematical extent,
  callback failure/divergence, and the overflowing successor. The public
  length replacement and rebase observer equivalences use this relation
  without representation, reads, cache/element laws, or successful maximum
  queries. The pending-update observer needs precisely equality of the actual
  emptiness-query results. At checkpoint `dab2f4e`, the full build passed
  (2,031 jobs), and the axiom/import audit validated 5,070 declarations across
  315 modules; all new lemmas use only standard Lean axioms. External models
  and roots are unchanged, so the model dependency gate was not repeated for
  this proof-only change.
- The packing-depth result is derived rather than assumed separately.
  `Tree/PackingDepth.lean` proves the actual depth computation from the optional
  factor query and its routing power law. `PackingLayout` drops the redundant
  depth-query premise in `0932572`, using the numeric foundation `69d2ec6`.
  A represented power-of-two factor fits in a word, so rounding returns that
  factor and trailing-zero counting returns its exponent. The `size_of`
  fallback is skipped and its axiom is unused. This removes a proof premise
  without changing numeric or option models; their broader source-fidelity
  review remains distinct from these kernel proofs.
  After the change, the full library builds (2,026 jobs), the axiom/import
  audit passes for 4,983 declarations across 310 modules, and the dependency
  inventory still passes for 42 roots and 151 local model declarations.
- Generic update-map, element clone/equality, codec, and generator calls use
  the operation-specific laws recorded in the proof coverage document. The
  dependency inventory does not verify concrete implementations of those laws.
  The earlier maximum-metadata audit established its exact criterion under
  unchanged raw map reads. It generalized clone, clone_from, and dependent
  rebase contracts to matching logical extent and derived successor safety
  internally, without assuming successful list-length evaluation or changing
  an external model. At that checkpoint the full build and axiom/import audit
  passed for 5,015 declarations across 314 modules (2,030 jobs); the separate
  dependency gate was not rerun for those proof-only changes. The subsequent
  lookup-agreement audit above also removes raw map-read identity.
  Fixed-encoder call equations in `Encode/FixedCalls.lean` now preserve the
  actual buffer fold, reservation checks, failure, and divergence without
  codec laws. Exact fixed-byte contracts separately bound reservation and
  payload size and restrict append laws to reached prefix buffers; they do
  not assume payload widths agree with metadata. The fixed decoder roundtrip
  still needs that agreement for chunk boundaries. These proof changes leave
  external models and API roots unchanged. Their full axiom/import audit
  passes for 4,993 declarations across 311 modules (2,027 build jobs); the
  separate dependency gate was not rerun for these proof-only changes.
  Subsequent variable-encoder proofs restrict append laws to preceding
  temporary payload buffers. `Encode/VariableCalls.lean` folds the actual
  external encoder calls and borrowed continuations through public reservation
  and finalization; `LengthCalls.lean` folds actual element size calls and
  checked additions before the final offset-table arithmetic. Both retain
  failure/divergence without codec/size laws or byte/offset bounds. They prove
  clients of the existing external definitions; they do not replace or
  independently establish the fidelity of those definitions.
  The full axiom/import audit passes after these changes for 5,012 declarations
  across 313 modules (2,029 build jobs), with no new axiom or admission. The
  external definitions and API roots remain unchanged, so the separate model
  dependency gate was not rerun for this proof-only checkpoint.
- Collection models preserve values and modeled logical size checks while
  abstracting allocation strategy and allocation failure. Their totality
  results are about the extracted model, not resource-exhaustion guarantees.
- Arc new/clone/deref/as_ref preserve pointee values in this model. Pointer
  equality has the existing explicit termination and one-way soundness axiom;
  heap identity and reference counts are not represented. No equal-values to
  equal-pointers converse is assumed.
- Lock accesses model the sequential value fragment. Contention, blocking,
  and shared cache writes are not represented. TreeHash/shared-write work is
  deferred; no change to Aeneas or the lock interface is claimed.
- The numeric, option, and container definitions, pinned SSZ/Arbitrary
  protocols, and entry footprints remain trusted definitions. This inventory
  identifies their use; kernel validation of their clients does not itself
  establish source-level fidelity or minimal theorem hypotheses.
- Borrowed CoW extraction and the remaining assumption/model-fidelity audit
  are incomplete. This gate is one part of that audit and does not complete
  the full goal.

The subsequent [borrowed-read reproducer](reproducers/cow_regions/README.md)
(`56924d0`) isolates the failed enum reference projection without map models.
Lifetime separation, a working nested-reference helper, and direct-copy
patterns do not resolve the eight tested readers. Four plain/nested/struct
controls extract and have axiom-free exact-value proofs. This narrows the
extraction boundary; no model of a milhouse borrowed method or partial
translation is substituted for the missing production body.

Initial inventory validation (`07ef38d`): the full library build passes
(2,023 jobs), and the valid environment
inventory was accepted. Eight deliberately invalid inventories were rejected:
missing summary/root records, a summary preceding its roots, a duplicated
dependency, an unknown model module, a root outside the generated module, an
inserted reference to the excluded identity model, and a local model replacing
a milhouse implementation. Both external-source edits were checked to contain
only comments; no proof or model definition changed. The
separate [axiom/import audit](PROGRESSIVE_LIST_PROOFS.md#validation) remains
required for changes to proofs or model definitions.
