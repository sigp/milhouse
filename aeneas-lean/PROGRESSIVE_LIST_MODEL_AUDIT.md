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

### Power comparison for both compiler-selector outcomes

Run `python3 scripts/aeneas-audit-pow-models.py`. The separate
[power source comparison](reproducers/pow_models/README.md) in `eb2f91b`
proves `core_pow_agrees`: the entire extracted `usize::pow` body equals the
local model for every base and exponent, including zero and exact overflow
failure. Both squaring loops are proved. Termination and the intermediate
overflow invariant are derived internally; there is no arithmetic-bound or
termination premise.

The compiler intrinsic remains an extraction boundary. The comparison
quantifies over an arbitrary Bool outcome, covering both allowed branches.
The checked outer body calls the selector at most once, so no repeated-call
consistency is assumed. Its generated selector class has only that Bool field,
without a default instance or axiom. The only change to generated `Funs.lean`
is a section parameter; removing it restores the original file exactly.
The report retains both file hashes, validates intrinsic source metadata and
the full caller shape, and records this under `parameterizedSourceComparisons`
and `abstractCompilerSelectors`. It never compiles the admitted template or
substitutes a power/loop body. Existing Aeneas scalar primitives remain trusted.

All eight source suites pass at this checkpoint: 33 direct comparisons, one
parameterized source comparison, and two compositions, totaling 36 proofs
(16 axiom-free, twenty standard-only). Four native power tests and four
Python provenance/control-flow tests also pass. The full library build and
axiom/import audit pass for 6,103 declarations across 429 modules; 5,984 use
only standard axioms or none, and 119 retain the existing Arc pointer contract.
The dependency gate passes for the unchanged 42 roots and 151 local model
declarations. No production Rust, production model, main extraction, or Aeneas
source changed. Borrowed CoW and other model-fidelity obligations remain open;
Debug, Serde, and TreeHash remain outside the current goal.

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

## Arbitrary source comparisons

Run `python3 scripts/aeneas-audit-arbitrary-models.py` from the repository root.
The [Arbitrary comparison](reproducers/arbitrary_models/README.md) validates
`nextControl` against actual `bool::arbitrary` in pinned `arbitrary` 1.4.1.
It includes the actual byte generator and `fill_buffer` source, proving the
one-byte copy/zeroing loop, write-back, termination, and low-bit interpretation.
For every input slice, both the Boolean answer and exact remaining input agree.
An even stopping byte is consumed; exhaustion succeeds with false and retains
empty input. There is no input, success, or termination premise.

The helper theorem covers the one-byte buffer reached by this control path,
not general buffer widths. Existing Aeneas array, slice, copy/index,
mutable-iterator, scalar, and Result foundations remain boundaries. The
source `Unstructured` is its actual extracted structure, compared through its
single byte-slice field. Its three error variants are mapped individually.

The runner checks the bool implementation's source module, distinguishing its
`arbitrary` method from the byte method with the same name. Type provenance
uses the dependency crate independently. Changing only the source error
type's final metadata name avoids a generated discriminant-instance collision;
restoring it must recover the entire original LLBC. Ten malformed source
inventories, ten invalid metadata/type-namespace cases, and four invalid axiom
reports are rejected.

At `db45ecc`, the comparison passes with only standard Lean axioms. Seven
native tests cover all 256 control values, repeated exhaustion, 768 one-byte
buffer overwrites, first-error and panic input state, generator input
replacement, owning-default dispatch, and size-hint defaults/overrides. All
seven source suites pass: 30 direct comparisons and two compositions,
totaling 32 proofs (16 axiom-free, sixteen standard-only).

The subsequent `e396dad` checkpoint adds direct source comparisons for both
size-hint defaults, for arbitrary dictionaries and depths. The fixed default
skips every callback. The fallible default calls the actual `size_hint` once,
preserving success, failure, or divergence without consistency, termination,
or depth premises. The complete source dictionary adapter retains all four
callbacks. Both proofs close by reflexivity; the fixed result uses only the
three standard Lean axioms, and the fallible result uses only `propext`.

The runner excludes the unused owning-input default and compares every field
of all three source declarations before and after, allowing only a checked
correspondence of fresh statement IDs. Charon's own statement equality ignores
these IDs. All nineteen renumberings are recorded; code, signatures, source
spans, and callable IDs must remain unchanged. A checked name-only adjustment
to the trait's first field avoids the generated namespace shadowing. Restoring
its two labels and the error type name must recover the entire original
selected LLBC. Nine malformed inventories, fifteen invalid trait/metadata
configurations, nine invalid exclusion/statement cases, and four invalid axiom
reports are rejected. Eight native tests pass, including hint panic dispatch.
All seven source suites pass: 32 direct comparisons and two compositions,
totaling 34 proofs (16 axiom-free, eighteen standard-only).

Full vector generation and the owning Arbitrary default remain source
boundaries. The owning default fails when ending the borrow of the real
`Unstructured`; vector extraction additionally fails on mutable iterator
borrows and collection adapters. The successful size-hint audit resolves the
unrelated default and naming obstacles as described above. No failed output
is used in a proof. Exact commands and diagnostics are in the fixture README
and UPSTREAM_BUGS issue 27. No production Rust, local model, or Aeneas source
changed; the main proof and 42-root/151-declaration inventories are unchanged.

## SSZ offset and encoder-construction source comparisons

Run `python3 scripts/aeneas-audit-ssz-offset-models.py` from the repository root.
The [SSZ offset comparisons](reproducers/ssz_offset_models/README.md) validate
the actual `ethereum_ssz` 0.10.0 four-byte constant and private `decode_offset`
body. The decoder comparison covers every input length, preserving exact
error fields and the four-byte little-endian value. It proves every iteration
of the actual slice-copy loop, checked increments, and termination, without
extra input, copy-success, or arithmetic premises.

A separate composition proof uses foundation prefix slicing and that extracted
decoder to establish the public `read_offset` model for every input. It is
explicitly not a successful direct extraction of the public body. All three
proofs use only standard Lean axioms and retain the existing byte, array,
slice/index, scalar, clone, and default foundations.

The runner validates the original transparent dependency provenance. It then
retains the private external decoder via its locality metadata and renames
the source error enum to avoid a generated instance-name collision with
`Tree.Types`. Reversing these two adjustments must recover the entire original
LLBC, including unchanged code, fields, IDs, call targets, and dictionaries.
Nine malformed inventories, eighteen invalid metadata/provenance/configuration
cases, and four invalid axiom reports are rejected.

At `c0d7c7f`, four native tests pass for short-input error payloads, all 32 bits
and extrema, mixed-byte order with ignored suffixes, and debug-profile
oversized-offset rejection. All six source suites pass: 29 direct comparisons
and two compositions, totaling 31 proofs (16 axiom-free, fifteen standard-only).
The main proof library and 42-root/151-declaration inventory are unchanged.

Direct public-reader extraction still fails with `There should be no bottoms
in the value` at the borrowed temporary. Offset encoding emits a reference to
the missing `core.num.Usize.to_le_bytes` foundation operation and cannot
elaborate. Exact reproduction commands and retained boundaries are in the
fixture README and UPSTREAM_BUGS issue 26. No assumed primitive, generated
body patch, production Rust change, or Aeneas change is introduced.

At `4cbc263`, the suite additionally compares the actual `SszEncoder::container`
body and its returned buffer-release continuation with the local model, for
every buffer and fixed-byte count. The proof uses only `propext` and requires
no bound or successful-reservation premise. It explicitly retains the existing
local `Vec::reserve` primitive; allocation, capacity, and reservation fidelity
are still boundaries.

The audit validates the primitive's `alloc` provenance and exact generated
template name/signature. The axiom template is never compiled. A module
containing only `import Tree.Ssz.Models` supplies the existing concrete
definition; no primitive or source body is added. Imports must be explicit
build targets and hashed model inputs, and the report records them under
`retainedLocalFoundations`. Seven malformed templates, seven invalid foundation
inventories, four invalid binding configurations, and four invalid axiom
reports are rejected. Other suites continue rejecting external templates
unless such a binding is explicitly declared and validated.

Eight native SSZ tests pass, including constructor release, reservation
overflow, payload movement/clearing, repeated finalization, and callback-panic
write order. Direct append and finalization extraction still fail on stored
mutable-buffer access (UPSTREAM_BUGS 26); native checks do not complete these
source obligations. All seven source suites pass: 33 direct comparisons and
two compositions, totaling 35 proofs (16 axiom-free, nineteen standard-only).
The main library and 42-root/151-declaration model inventory are unchanged.
Append/finalize, reservation fidelity, and the remaining SSZ/model/assumption
review stay open.

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

- The binary selection necessity review (`3cf17f1`, progressive/list necessity
  `22b4d2f`, binary necessity `453ef4c`) removes the remaining upfront numeric
  binary selection condition from the materialization criteria. Successful
  selected children rebuild to nonzero trees; dense output therefore forces their
  lengths positive. Binary `Selection.lean` proves that every selected query starts
  inside the final occupied window, using layout, prefix alignment, successful
  execution, and output density. It needs no input invariant, offset alignment,
  capacity, clone, range-value, or termination law. A clipped-prefix corollary
  converts the local occupied length to a global logical endpoint.

  `ProgressiveTree/BulkUpdate/BinarySelection.lean` recovers both an actual
  successful binary result and its exact clipped dense length at each selected
  layer. It then lifts numeric selection necessity to recursive and public
  progressive rebuilding. `ApplyUpdates/BinarySelection.lean` derives the condition
  from successful nonempty application and dense output alone, with layout but
  without input representation/backing, output capacity, default, clone, range,
  or termination assumptions.

  The new successful-result criterion in `SkippedConditions.lean` needs only
  layout and input representation/backing validity upfront. Selected clone
  identity, numeric selection, and all skipped-value agreements are jointly
  necessary and sufficient for valid materialization after actual success.
  `InputConditions.lean` gives four exact existence criteria, with or without
  final representation and across both branches. Positive binary selection is
  now on the necessary-and-sufficient side alongside reached-query termination,
  `BulkCloneLaws`, missing-update guards, progressive selection, all skipped-value
  agreements, final occupied capacity, and actual default construction. The
  representation variants additionally require the actual default map's exact
  extent and self-overlay.

  No separate clone, range, termination, guard-success, final-capacity, or
  default-success law is assumed upfront by those existence criteria. Layout and
  input representation/backing validity remain the explicit rebuilding
  preconditions. The no-op needs valid backing already storing the contents and
  no rebuilding conditions; its representation variant uses input representation.
  All existing public theorem names remain available. This closes binary
  selection necessity for these materialization contracts; it does not establish
  raw success alone implies density or complete the remaining input/geometry
  and model-fidelity audits.

  Focused and full builds pass (2,145 jobs). The axiom/import audit covers
  6,103 declarations across 429 modules: 5,984 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. All 11 new public lemmas
  use standard Lean axioms; private/generated declarations are included in the
  inventory. No new axiom or admission was introduced. External axiom use is
  unchanged, and `size_of` remains unused. Existing execution, total, and cache
  proofs validate.

  Work remains on geometry and input assumptions, borrowed CoW, and model
  fidelity. No Rust, extraction, external model, or Aeneas source changed; the
  seven source suites and 42-root/151-declaration dependency gate were not
  repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
  is deferred outside the goal.
- The skipped-binary materialization review (`5108135`, successful-result
  criterion `92b365d`, total contracts `a8455fa`, progressive/list contents
  `24607a2`, selected-layer reads and scope `3a7d3ce`) removes pending-value
  exclusion and reflection from selected-layer read-back, progressive contents,
  list materialization, and complete total correctness. Matching redundant updates
  may now be skipped inside binary windows as well as progressive layers and
  maximum-skipped suffixes. The conditions refer to actual input observations and
  original slots, without assuming a rebuilding result.

  The generalized layer and progressive contents proofs use binary skipped-value
  agreement alongside retained/pending clone identity and the existing progressive
  layer/suffix agreements. `ApplyUpdates/Contents.lean` derives every final backing
  read without density or default-map laws. `Materialized.lean` combines these
  reads with the weaker backing-density contracts to identify the exact stored
  sequence. The new nonempty and all-branch `_total_spec_of_guards` contracts
  also derive execution, representation, backing validity, and the pending
  observer, under the actual default map's extent, overlay, and emptiness laws.
  The older sufficient contracts retain their signatures as adapters.

  `SkippedConditions.lean` characterizes valid materialization after actual
  nonempty success by retained/pending identity, positive progressive selection,
  and agreement in all three skipped scopes. No clone or range-value law is
  assumed upfront. Layout, input representation/backing validity, and positive
  numeric binary selection remain explicit. The default map is unconstrained.

  `SelectionConditions.lean` gives four exact existence criteria for valid
  materialization, with or without final representation, on the nonempty branch
  and across both branches. Occupied capacity, reached-query termination, copied
  storage termination plus retained/pending identity, missing-update guards,
  positive progressive selection, all skipped-value agreements, and actual default
  construction are on the necessary-and-sufficient side. No range-value reflection
  or upfront clone, termination, guard-success, or default-success law is required.
  Final occupied capacity is part of the criterion. Representation additionally
  requires exact default-map extent and self-overlay. The no-op requires valid
  backing already storing the contents, with no rebuilding conditions; its
  representation variant uses input representation.

  Positive numeric selection inside binary subtrees remains an upfront condition
  on rebuilding: a true answer must select a window starting inside the final
  prefix. Proving this condition necessary and moving it into the exact criterion
  is unfinished. These results do not claim that raw success alone establishes
  valid backing or correct contents, or that all hypothesis audits are complete.

  Focused and full builds pass (2,141 jobs). The axiom/import audit covers
  6,069 declarations across 425 modules: 5,950 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. All 19 new public lemmas
  use standard Lean axioms; private/generated declarations are included in the
  inventory. No new axiom or admission was introduced. External axiom use is
  unchanged, and `size_of` remains unused. Existing execution, total, and cache
  proofs validate.

  Work remains on binary selection necessity, geometry and other assumptions,
  borrowed CoW, and model fidelity. No Rust, extraction, external model, or Aeneas
  source changed; the seven source suites and 42-root/151-declaration dependency
  gate were not repeated for this proof-only work. Debug and Serde remain excluded;
  TreeHash is deferred outside the goal.
- The binary density range review (`82f8265`, binary skipped extents `4446f3e`,
  progressive/list numeric contracts `3bbf03b`, binary density `a44efeb`, local
  reflection adapter `0fefbab`) removes pending-value range reflection from
  backing-density preservation. Reached ranges need only numeric effects:
  skipped windows keep their occupied length, and selected windows start inside
  the final prefix. The generalized binary proof clips global prefix endpoints
  to each child window. The prior binary, progressive, and list reflection
  contracts retain their signatures as adapters.

  `Tree/BulkUpdate/SkippedExtents.lean` derives false-answer extent preservation
  from agreement with original dense slots. Otherwise a newly required extension
  value would have to match a missing old slot. This uses input density, prefix
  alignment, and local monotonicity/extension completeness, without an update
  result, packing-operation law, machine-capacity bound, clone law, or range-value
  law. Its density corollary combines that agreement with numeric positive
  selection. `ProgressiveTree/BulkUpdate/BinarySkippedExtents.lean` lifts the
  false-answer result through selected-layer slot routing using input density,
  layout, and the extension laws, without input capacity or successful rebuilding.

  The new progressive density and list backing contracts accept numeric conditions
  for both progressive and binary ranges. Their skipped-range variants derive all
  false-answer extent conditions from agreement with original values, leaving only
  positive numeric selection independent. `apply_updates_preserves_backing_of_skipped_ranges`
  proves backing validity on every successful application from input representation
  and backing validity, with layout and reached range conditions only on the
  rebuilding branch. Representation supplies the dense update domain, and actual
  checked length supplies the maximum's numeric bound. No clone identity,
  clone termination, range termination, or default-map law is assumed.

  These are preservation theorems conditional on actual success. The separate
  execution criteria use the previously proved missing-update guards without
  range correctness. The public valid-materialization existence criteria still
  retain selected binary reflection: the weaker binary content conditions must
  be lifted through the progressive/list sufficient proofs and combined with
  these density contracts. Necessity of the remaining binary numeric selection
  conditions also needs proof. Correct stored contents, valid backing, and
  successful execution remain distinct obligations.

  Focused and full builds pass (2,139 jobs). The axiom/import audit covers
  6,051 declarations across 423 modules: 5,932 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. All 14 new public lemmas
  use standard Lean axioms; private/generated declarations are included in the
  inventory. No new axiom or admission was introduced. External axiom use is
  unchanged, and `size_of` remains unused. Existing execution, total, and cache
  proofs validate.

  Work remains on materialization criteria, selection necessity, geometry and
  other assumptions, borrowed CoW, and model fidelity. No Rust, extraction, external
  model, or Aeneas source changed; the seven source suites and
  42-root/151-declaration dependency gate were not repeated for this proof-only
  work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.
- The missing-update guard review (`d1c91b1`, progressive contracts `676a3a5`,
  binary contracts `2998487`, necessity `2224494`, scope `bcefc21`) removes
  range correctness from binary, progressive, and public list execution proofs.
  `BulkGuardsPass` states the actual missing-update checks: an unpacked terminal
  needs a pending value; an internal node cannot have both child queries return
  false, and selected children must pass their own guards. Packed terminals need
  no pending-value witness. This condition uses input geometry and actual map
  answers, without assuming an update result or query termination.

  Successful binary execution implies these guards under layout, input shape,
  and prefix alignment, without range, clone, termination, density, or capacity
  laws. Selected-layer scopes lift necessity to progressive rebuilding and list
  application. The generalized sufficient execution proofs use these guards and
  reached-query termination instead of binary range reflection. Previous
  `_of_enabled` contracts retain their signatures as adapters from their stronger
  pending-witness and reflection laws.

  `ApplyUpdates/GuardConditions.lean` proves exact execution criteria for nonempty
  application and both branches. On the rebuilding branch, input representation,
  density, layout, occupied capacity, and selected clone termination remain
  upfront. Reached range-query termination, selected guards, and an actual
  successful default construction are on the necessary-and-sufficient side.
  No range correctness, assumed guard success, or upfront query/default success
  is required. The empty-map no-op has no rebuilding conditions.

  These are execution criteria. The existing binary contents criterion separately
  uses retained/pending clone identity and skipped-value agreement without range
  correctness. Public valid-materialization criteria still use selected binary
  reflection: weakening backing-density preservation and connecting the weaker
  content conditions remain unfinished. Successful execution alone does not
  establish valid backing or correct stored contents for incoherent map answers.

  Focused and full builds pass (2,136 jobs). The axiom/import audit covers
  6,008 declarations across 420 modules: 5,889 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. All 19 new public lemmas
  use standard Lean axioms; private/generated declarations are included in the
  inventory. No new axiom or admission was introduced. External axiom use is
  unchanged, and `size_of` remains unused. Existing success, total, and cache
  proofs validate.

  Backing-density range premises, geometry and other assumption minimality,
  borrowed CoW, and model fidelity remain unfinished. No Rust, extraction,
  external model, or Aeneas source changed; the seven source suites and
  42-root/151-declaration dependency gate were not repeated for this proof-only
  work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.
- The binary skipped-value review (`30c17f3`, binary equivalence/selected
  content bridge `8d17355`, generalized contents `7a2235e`, scope/routing
  `79282b8`) weakens content preservation from exclusion of pending values in
  skipped binary ranges to agreement with their original slots. Matching redundant
  updates may be skipped. The condition uses only the original tree, geometry,
  and reached range answers, without any rebuilding result. The generalized
  shape/capacity/content and extracted read-back contracts accept this weaker
  law; existing exclusion contracts remain adapters with unchanged signatures.

  Actual successful binary rebuilding preserves every slot in a reached range
  answered false. This uses layout and prefix alignment, without input shape,
  density, capacity, offset alignment, range, clone, or termination laws. Correct
  binary contents therefore force skipped-value agreement. Combined with retained
  clone necessity, `with_updated_leaves_contents_iff_clones_skipped` characterizes
  correct binary contents by retained/pending identity and skipped-value agreement,
  with no range-correctness law in either direction. Layout, input shape, alignment,
  and actual successful execution remain explicit in the equivalence.

  The selected progressive content bridge and progressive/list `BinarySkipped.lean`
  modules lift agreement necessity to successful dense list materialization.
  Progressive necessity needs layout and correct mathematical slots, with no input
  shape or density law. List necessity derives those slots from input representation
  and backing validity plus dense output storing the exact contents; no output
  capacity, range, maximum, default, clone, or termination law is assumed.
  These results do not yet remove selected binary reflection from public
  valid-materialization existence criteria: binary execution and backing-density
  proofs still use it.

  Focused and full builds pass (2,131 jobs). The axiom/import audit covers
  5,962 declarations across 415 modules: 5,843 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. All 19 new public lemmas
  use standard Lean axioms; private/generated declarations are included in the
  inventory. No new axiom or admission was introduced. External axiom use is
  unchanged, and `size_of` remains unused. Existing success, total, and cache
  proofs validate.

  Remaining binary execution/density range premises and geometry minimality,
  borrowed CoW, and model fidelity are unfinished. No Rust, extraction, external
  model, or Aeneas source changed; the seven source suites and
  42-root/151-declaration dependency gate were not repeated for this proof-only
  work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.
- The progressive/list clone-identity review (`6f2915e`, list necessity
  `5e01cf9`, progressive necessity `18b4833`, selected slots `b1246e7`) proves
  that successful dense materialization forces every selected pending clone and
  retained stored clone to preserve its value. Selected-slot routing recovers
  both the original binary input and its actual rebuilt result without shape,
  density, range, clone, or termination laws. Progressive necessity uses layout,
  input shape, and correct mathematical suffix slots, with no capacity law.
  At the list boundary, input representation and backing validity supply the
  overlay; output density and exact stored contents supply correctness, without
  assuming output capacity validity or any range, maximum, default, or clone law.

  Four public existence criteria now assume no clone or termination law upfront.
  Selected `BulkCloneLaws` appear on the necessary-and-sufficient side, combining
  termination of all copied storage with identity only for retained slots and
  pending values. Overwritten stored copies may change value. Query termination,
  start, occupied capacity, positive progressive selection, skipped-layer/suffix
  agreement, and actual default construction remain part of the criterion.
  Selected binary reflection, layout, and input invariants remain upfront.
  The representation variants add exact default-map extent and self-overlay;
  the no-op requires valid backing already storing the contents and no rebuilding
  laws. Output backing validity remains part of the result, so stored-list
  equality alone is a weaker observation.

  Focused and full builds pass (2,125 jobs). The axiom/import audit covers
  5,897 declarations across 409 modules: 5,778 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. All ten new public lemmas
  use standard Lean axioms; private/generated declarations are included in the
  inventory. No new axiom or admission was introduced. External axiom use is
  unchanged, and `size_of` remains unused. Existing success, total, and cache
  proofs validate.

  Binary range and geometry minimality, borrowed CoW, and model fidelity remain
  unfinished. No Rust, extraction, external model, or Aeneas source changed;
  the seven source suites and 42-root/151-declaration dependency gate were not
  repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
  is deferred outside the goal.
- The clone-identity review (`c3b836b`, terminal/routing lemmas `ba2a10c`,
  packed identity `e6ea416`, actual clone tracking `1bc9b38`) proves that correct
  binary update contents force identity for every selected pending clone and
  retained stored clone. Actual vector/packed reads preserve the returned clone
  values without identity or termination assumptions. Packed-window correctness
  is exactly retained/pending identity; overwritten stored copies need no
  identity law. The binary proof follows selected children and zero expansion,
  using layout, input shape, and alignment, without range correctness, density,
  capacity, clone, or termination laws. Under exclusion of pending values from
  skipped binary windows, the existing converse gives an equivalence.

  These are lower-level results. Propagating identity necessity to progressive
  and list materialization remains unfinished; the public existence criteria
  still assume retained/pending identity, selected binary reflection, layout,
  and input invariants. Their previously derived query/stored-clone termination
  and start conditions remain on the necessary-and-sufficient side, alongside
  capacity, selection, skipped-value agreement, and actual default construction.
  No rebuilding law is added to the no-op branch.

  Focused and full builds pass (2,121 jobs). The axiom/import audit covers
  5,875 declarations across 405 modules: 5,756 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. All 13 new public lemmas
  use standard Lean axioms; private/generated declarations are included in the
  inventory. No new axiom or admission was introduced. External axiom use is
  unchanged, and `size_of` remains unused. Existing success, total, and cache
  proofs validate.

  Remaining progressive/list identity, binary range, and geometry minimality,
  borrowed CoW, and model fidelity are unfinished. No Rust, extraction, external
  model, or Aeneas source changed; the seven source suites and
  42-root/151-declaration dependency gate were not repeated for this proof-only
  work. Debug and Serde remain excluded; TreeHash is deferred outside the goal.
- The query-termination review (`09b6d34`, progressive/list necessity `ceb502f`,
  complete scope `0095ccd`, binary necessity and geometry-step helper `b6b4338`)
  proves that successful rebuilding certifies every reached range query.
  `BulkRangeOn` is exactly the union of progressive layer queries and queries
  inside selected binary layers. Progressive layer termination needs no metadata,
  input invariant, clone, or range-correctness law; empty layer windows do not
  call the external map. Binary necessity needs layout and prefix alignment, with
  no shape, density, capacity, clone, lookup, or range-correctness law. Complete
  progressive and public list necessity need only layout on nonempty application.
  Four public existence criteria now remove the upfront query-termination law.
  Termination of reached queries joins stored-clone termination, start, occupied
  capacity, positive selection, skipped-layer/suffix agreement, and an actual
  default outcome on the necessary-and-sufficient side. The criteria cover valid
  materialization, with or without final representation, on the rebuilding branch
  and across both branches. The remaining upfront clone/range laws are identity
  on retained slots and selected pending values and reflection in selected binary
  subtrees; layout and input invariants remain explicit. Final representation
  adds exact default extent and self-overlay; pending emptiness is a separate
  observer law. The no-op needs valid backing already storing the contents and
  no rebuilding query or clone condition; its representation variant uses input
  representation. Output backing validity is included, so equality of stored
  lists alone is a weaker observation.
  Focused and full builds pass (2,118 jobs). The axiom/import audit covers
  5,818 declarations across 402 modules: 5,699 use only standard Lean axioms or
  none, and 119 use the existing Arc pointer contract. The 11 new lemmas and
  newly public geometry-step helper use standard Lean axioms; private/generated
  declarations are included in the inventory. No new axiom or admission was
  introduced. External axiom use is unchanged, and `size_of` remains unused.
  Existing success, total, and cache proofs validate.
  Remaining retained-identity, binary range, and geometry minimality, borrowed
  CoW, and model fidelity are unfinished. No Rust, extraction, external model, or
  Aeneas source changed; the seven source suites and 42-root/151-declaration
  dependency gate were not repeated for this proof-only work. Debug and Serde
  remain excluded; TreeHash is deferred outside the goal.
- The preceding skipped-layer review (`5a9398e`, read criterion `5481b38`, necessity
  `84224a8`, capacity geometry `f146b17`, contents `b53be68`/`bacc216`,
  bounds/scope `f3248ed`/`2f3e7bc`) weakens false progressive range answers
  from pending-value exclusion to agreement with unchanged input reads.
  Scoping uses actual geometry and range/maximum observations, with no assumed
  rebuilding result. Successful capacity calculations supply metadata success
  and monotonicity, so complete read preservation in skipped layers needs no
  packing, shape, clone, range-correctness, or lookup-termination law. The
  public read and stored-materialization criteria prove agreement in skipped
  layers and suffixes necessary and sufficient under the remaining selected
  clone/binary laws and, for stored contents, numeric layer extents. Defaults
  are unconstrained. Existing stronger contracts are adapters; success/total
  and cache contracts validate but retain stronger range laws.
  The full build passes (2,097 jobs), and the axiom/import audit covers 5,667
  declarations across 381 modules: 5,548 use only standard Lean axioms or none,
  and 119 use the existing pointer contract. All 22 new named lemmas use only
  standard Lean axioms; private/generated helpers are included in the inventory.
  External axiom use is unchanged. No new axiom or admission was introduced,
  and `size_of` remains unused. No Rust, extraction, external model, or Aeneas
  source changed. The seven source suites and 42-root/151-declaration dependency
  gate were not repeated for this proof-only work. Necessity of numeric layer
  extents, binary range/clone/geometry minimality, borrowed CoW, and model
  fidelity remain open. Debug and Serde remain excluded; TreeHash is deferred.
- The preceding layer-range review (`3780516`, density `2416785`, empty-layer bounds
  `01415b8`, scope `78cacde`) separates numeric occupied-length conditions at
  progressive layers from pending-value reflection within selected binary
  subtrees. A false layer answer need only preserve its occupied length;
  a true answer starts inside the final prefix. These scopes use actual input
  geometry and range/maximum observations, without a rebuilding result.
  Density, public backing preservation, occupied-capacity certification, and
  both actual-rebuilt-value representation criteria use the weaker conditions.
  Existing reflection contracts are adapters using the input representation.
  Content/materialization and termination contracts retain stronger range
  laws; those and the cache contracts validate. The full build passes
  (2,093 jobs), and the axiom/import audit covers 5,630 declarations across
  377 modules: 5,511 use only standard Lean axioms or none, and 119 use the
  existing pointer contract. All 21 new named lemmas use only standard Lean
  axioms; private/generated helpers are included in the inventory. External
  axiom use is unchanged. No new axiom or admission was introduced, and
  `size_of` remains unused. No Rust, extraction, external model, or Aeneas
  source changed. The seven source suites and 42-root/151-declaration
  dependency gate were not repeated for this proof-only work. Necessity of
  the numeric layer conditions, binary range/clone/geometry minimality,
  borrowed CoW, and model fidelity stay open. Debug and Serde remain excluded;
  TreeHash remains deferred.
- The materialization review (`dda608d`, equivalence `034d26b`, suffix reads
  `19dee5c`) proves skipped-value agreement necessary for exact materialization.
  Actual successful traversal preserves complete read results on selected
  skipped suffixes without packing, shape, clone, or range-correctness laws;
  the guards themselves route ancestor reads. The public necessity result
  needs neither input representation nor default-map laws. Under selected
  clone/range and backing laws, agreement is equivalent to correct backing
  reads and exact stored contents. Successful materialization has an exact
  occupied-capacity/agreement/default-construction criterion, with actual
  default overlay and extent additionally required for final representation.
  The no-op branch stores the merged sequence exactly when the input backing
  already does; rebuilding laws remain conditional on nonempty application.
  The existing sequence criterion reuses the combined materialization result;
  total and cache contracts validate. Necessity concerns materialization;
  the separate representation criterion allows the installed map to compensate
  for different stored values. The full build passes (2,091 jobs), and the
  axiom/import audit covers 5,600 declarations across 375 modules: 5,481 use
  only standard Lean axioms or none, and 119 use the existing pointer contract.
  All 10 new named lemmas use only standard Lean axioms; private/generated
  helpers are included in the inventory. External axiom use is unchanged.
  No new axiom or admission was introduced, and `size_of` remains unused. No
  Rust, extraction, external model, or Aeneas source changed. The seven source
  suites and 42-root/151-declaration dependency gate were not repeated for this
  proof-only work. Selected clone/range and geometry minimality, borrowed CoW,
  and model fidelity stay open. Debug and Serde remain excluded; TreeHash
  remains deferred.
- The skipped-suffix review (`10c8634`, list contents `592280c`, bulk contents
  `ad51425`, scope `25f577f`) replaces the global semantic maximum bound in
  generalized content, materialization, total, and success/representation
  contracts with agreement of present pending values in selected skipped
  suffixes. The scope follows actual geometry/range/maximum observations on
  the input tree and contains no rebuilding call or result. Only values in
  the new logical prefix must agree with unchanged suffix reads; redundant
  matching entries beyond the reported maximum are allowed. The checked
  length supplies the numeric extent bound. Old maximum-bound and empty-map
  contracts remain adapters; cache contracts validate. The full build passes
  (2,088 jobs), and the axiom/import audit covers 5,583 declarations across
  372 modules: 5,464 use only standard Lean axioms or none, and 119 use the
  existing pointer contract. All 15 new named lemmas use only standard Lean
  axioms; generated helpers are included in the inventory. External axiom use
  is unchanged. No new axiom or admission was introduced, and `size_of` remains
  unused. No Rust, extraction, external model, or Aeneas source changed. The
  seven source suites and 42-root/151-declaration dependency gate were not
  repeated for this proof-only work. Necessity of the remaining selected
  clone/range/skipped-value premises, geometry minimality, borrowed CoW, and
  model fidelity stay open. Debug and Serde remain excluded; TreeHash remains
  deferred.
- The maximum-premise review (`aa023cf`, lower proofs `f0daba3`) removes
  `MaximumBoundsValues` from `apply_updates` backing preservation, both
  occupied-capacity criteria, and both actual-rebuilt-value representation
  criteria. The actual checked length calculation supplies the numeric
  extension bound required by the generalized bulk-density proof. The old
  lower density contracts remain as adapters. Content-preservation,
  materialization, and total sequence contracts retain the semantic maximum
  law for skipped pending values; that premise remains under review. Existing
  total and cache contracts validate. The full build passes (2,087 jobs), and
  the axiom/import audit covers 5,566 declarations across 371 modules: 5,447
  use only standard Lean axioms or none, and 119 use the existing pointer
  contract. The three new lower lemmas and five strengthened public lemmas
  use only standard Lean axioms; generated helpers are included in the
  inventory. External axiom use is unchanged. No new axiom or admission was
  introduced, and `size_of` remains unused. No Rust, extraction, external
  model, or Aeneas source changed. The seven source suites and
  42-root/151-declaration dependency gate were not repeated for this proof-only
  work. Borrowed CoW and the remaining assumption/model-fidelity audit stay
  open. Debug and Serde remain excluded; TreeHash remains deferred.
- `apply_updates` now has exact representation criteria using the actual
  rebuilt values and installed-map overlay/extent, without a separate clone-
  identity or empty-default law. Actual backing reads are derived independently
  of the default map, and selected clone preservation identifies the complete
  stored sequence. Total contracts use exact default-map laws, retaining the
  existing empty-map contracts as adapters. Under selected clone and range/
  maximum assumptions, successful preservation is equivalent to the actual
  empty no-op or occupied final capacity and an actual default outcome with
  those laws. Rebuilding premises are conditional on the nonempty branch;
  pending emptiness supplies only its observer. Complete length-result equality
  has an exact extent criterion without representation, geometry, clone,
  range, or successful-metadata assumptions, including unchanged failure and
  divergence on the no-op branch. Length integration is `8e80e9c`, success
  criteria `5823c1f`, total contracts `40ac435`, materialization `decf6f7`, and
  overlay foundation `c338515`. These results audit default-map conditions
  under stated premises; they do not complete clone/range/geometry minimality
  or external-model source fidelity. Borrowed CoW remains open. The full build
  passes (2,087 jobs), and the axiom/import audit covers 5,558 declarations
  across 371 modules: 5,439 use only standard Lean axioms or none, and 119 use
  the existing pointer contract. All nine new named lemmas use only standard
  Lean axioms; generated helpers are included in the inventory. External axiom
  use is unchanged. No new axiom or admission was introduced, and `size_of`
  remains unused. No Rust, extraction, external model, or Aeneas source changed.
  The seven source suites and 42-root/151-declaration dependency gate were not
  repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
  remains deferred.
- Both Arbitrary generator entry points now have exact representation and
  success criteria using the actual default map's overlay/extent, finite
  control/element traces, and occupied-layer `LengthFits`. The successful
  trace retains the actual final input; the owning default existentially
  recovers the state discarded by its ordinary generator call. No trace,
  successful default construction, element-consumption law, or size hint is
  assumed by the equivalences. Generalized total and successful-state
  contracts derive representation and valid backing/spine, using pending
  emptiness only for its observer. Existing empty-map contracts are adapters.
  Owning integration is `16befa3`, ordinary success and total contracts
  `f93004f`, and representation foundation `b8f058f`. These results audit
  default-map laws under the stated layout and external generator model;
  they do not complete geometry/premise minimality or source-fidelity review.
  Borrowed CoW remains open. The full build passes (2,084 jobs), and the
  axiom/import audit covers 5,547 declarations across 368 modules: 5,428 use
  only standard Lean axioms or none, and 119 use the existing pointer contract.
  All nine new lemmas use only standard Lean axioms; external axiom use is
  unchanged. No new axiom or admission was introduced, and `size_of` remains
  unused. No Rust, extraction, external model, or Aeneas source changed. The
  seven source suites and 42-root/151-declaration dependency gate were not
  repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
  remains deferred.
- Public decoding now has exact default-map representation and success
  criteria tied to actual consumed payloads. The trace total contract derives
  execution, represented contents, valid backing, exact stored values/count,
  and installed map; both canonical-format total contracts also use the exact
  overlay and extent laws. Existing empty-map contracts remain adapters.
  Pending emptiness supplies only its observer. Empty bytes bypass packing
  and element metadata, and `represents_nil_iff` proves that zero backing
  length, absent maximum, and absent reads are precisely the empty sequence's
  representation requirements without a tree or packing law. Public format
  integration is `decd3f9`, trace criteria `5c49998`, and representation
  foundation `5b8202a`. The full build passes (2,082 jobs); the axiom/import
  audit covers 5,538 declarations across 366 modules: 5,419 use only standard
  Lean axioms or none, and 119 use the existing pointer contract. All nine
  named new lemmas and two generated helpers use only standard Lean axioms;
  external axiom use is unchanged. No new axiom or admission was introduced,
  and `size_of` remains unused. These proofs audit default-map laws under the
  stated packing and decoding premises; they do not finish geometry, codec-
  premise, or external-model fidelity review. At that checkpoint, Arbitrary's
  default-map audit and borrowed CoW remained open. No Rust, extraction,
  external model, or Aeneas source changed. The seven source suites and
  42-root/151-declaration dependency
  gate were not repeated for this proof-only work. Debug and Serde remain
  excluded; TreeHash remains deferred.
- All four sequence constructors now have exact success and representation
  criteria using the actual default map's overlay and
  logical extent. Redundant matching entries and maxima below the input
  length are allowed; empty-map laws are sufficient adapters. Iterator success
  supplies the actual consumed sequence and proves its equality to stored
  values, while vector callers need no iterator premise. Generalized total
  contracts derive execution, representation, valid backing, and valid spine;
  pending emptiness is separate and used only for its observer. The criteria
  are `a756c07`, total contracts `a32454f`, and foundation `75701ea`. Packing
  layout and geometry remain explicit; these results do not establish full
  premise minimality or external-model fidelity. Borrowed CoW and remaining
  assumption/model-fidelity review are incomplete. The full build passes
  (2,080 jobs), and the axiom/import audit covers 5,527 declarations across
  364 modules: 5,408 use only standard Lean axioms or none, and 119 use the
  existing pointer contract. All twelve new lemmas use only standard Lean
  axioms; external axiom use is unchanged. No new axiom or admission was
  introduced, and `size_of` remains unused. No Rust, extraction, external
  model, or Aeneas source changed. The seven source suites and 42-root/
  151-declaration dependency gate were not repeated for this proof-only work.
  Debug and Serde remain excluded; TreeHash remains deferred.
- Front-removal representation now uses the exact default-map overlay and
  logical extent over the actual ordered clones. Clone identity, absent map
  entries, and an absent maximum are not separately required. The public
  success-and-representation criterion combines those outcomes with the
  removal bound and retained capacity, omitting clone/default laws on zero
  removal and using packing/traversal laws only for a nonzero in-bounds rebuild.
  The complete nonzero contract derives all calls, represented suffix, valid
  backing, exact cloned contents, recorded length, and installed map; a
  separate emptiness law supplies only the pending observer. The general
  same-length dense-backing representation equivalence and existing content/
  total adapters use only standard Lean axioms. Public integration is `45f8783`,
  with `7801d06` and `9dd67d2` as foundations. These results audit clone/default
  laws under the stated input representation and geometry, without asserting
  minimality of all premises or source fidelity of the external models.
  Borrowed CoW and the remaining assumption/model-fidelity work are incomplete.
  The full build passes (2,078 jobs), and the axiom/import audit covers 5,515
  declarations across 362 modules: 5,396 use only standard Lean axioms or none,
  and 119 use the existing pointer contract. All five new lemmas use only
  standard Lean axioms; external axiom use is unchanged. No new axiom or
  admission was introduced, and `size_of` remains unused. No Rust, extraction,
  external model, or Aeneas source changed. The seven source suites and
  42-root/151-declaration dependency gate were not repeated for this proof-only
  work. Debug and Serde remain excluded; TreeHash remains deferred.
- Rebase read and representation contracts now identify the exact clone
  conditions. In-place rebasing preserves all public read results without
  representation or map-read-success premises. For nonmutating rebasing,
  fallback-aware agreement with the actual cloned map is necessary and
  sufficient for complete read equality; matching logical extent additionally
  characterizes preservation of a represented sequence. Successful preserving
  execution is equivalent to selected backing readiness and an actual map
  clone with those read/extent outcomes. Both total contracts derive execution
  and the complete representation/backing/metadata result, and existing
  content/total/cache contracts now use them. Public integration is `594f218`,
  with `eef66e2` and `297cfd4` as foundations. Layout and backing geometry
  justify traversal, and selected content soundness remains explicit. This
  proves necessity of the clone laws under those premises; it does not finish
  all semantic-premise or model-fidelity review. Borrowed CoW remains open.
  The full build passes (2,075 jobs), and the axiom/import audit covers 5,510
  declarations across 359 modules: 5,391 use only standard Lean axioms or none,
  and 119 use the existing pointer contract. Ten new declarations reuse it;
  no new axiom or admission was introduced, and `size_of` remains unused.
  No Rust, extraction, external model, or Aeneas source changed. The seven
  source suites and 42-root/151-declaration model dependency gate were not
  repeated for this proof-only work. Debug and Serde remain excluded; TreeHash
  remains deferred outside the current goal.
- The selected cache criteria now cover both public rebase methods without
  layout, geometry, density, capacity, accurate-length, query-success, map,
  or representation premises. Under selected content soundness and actual
  success, `RebaseCacheInputs` is necessary and sufficient for result cache
  validity. The scope follows supplied binary metadata, actual progressive
  packing results, and clamped lengths. Immediate stops require original
  suffix caches; entered progressive roots retain their original caches.
  Existing cache proofs use the general result through dense-input adapters.
  Both action-classifier reflection proofs now use only standard Lean axioms,
  removing their former use of the pointer contract. Public integration is
  `e88ce19`, with `2307f24`, `c20e293`, `c31c8bb`, `9db36ad`, and `f9da88a` as
  foundations. This is an assumption audit of clients of the existing model;
  it does not establish external-model fidelity or minimality of all selected
  content soundness obligations. Borrowed CoW and the remaining assumption
  and model-fidelity work are incomplete.
  The full build passes (2,072 jobs), and the axiom/import audit covers 5,497
  declarations across 356 modules: 5,388 use only standard Lean axioms or none,
  and 109 use the existing pointer contract. Five new cache-equivalence
  declarations use the contract, and the existing classifier no longer does.
  No new axiom or admission was introduced; `size_of` remains unused. No Rust,
  extraction, external model, or Aeneas source changed; the seven source suites
  and 42-root/151-declaration dependency gate were not repeated. Debug and Serde
  remain excluded, and TreeHash remains deferred outside the current scope.
- Selected content proofs now preserve exact materialized backing contents
  for both public rebase methods from actual success and `RebaseContentInputs`,
  without packing layout, global query success, shape, density, capacity, or
  accurate-length premises. The binary scope follows actual optional metadata;
  the progressive scope follows actual query results and clamped lengths.
  Existing content contracts use the general proof through dense-input
  adapters. New merged-sequence contracts retain geometry/layout for indexed
  traversal and the existing nonmutating map-clone read/extent laws. Semantic
  soundness remains explicit; necessity and complete assumption minimality are
  not claimed. Public integration is `c8724e7`, with `78d9600`, `b166ec0`,
  `aa0bb68`, `5832bf5`, `47c372e`, and `1fa4dbc` as foundations. This proof-only
  change does not establish source fidelity of external definitions. Borrowed
  CoW, remaining assumption review, and model fidelity remain incomplete.
  The full build passes (2,065 jobs), and the axiom/import audit covers 5,450
  declarations across 349 modules: 5,345 use only standard Lean axioms or none,
  and 105 use the existing pointer contract. Eight additional declarations
  reuse that contract; no new axiom or admission was introduced, and `size_of`
  remains unused. No Rust, extraction, external model, or Aeneas source changed;
  the seven source suites and 42-root/151-declaration model dependency gate
  were not repeated. Debug and Serde remain excluded; TreeHash is deferred.
- `Rebase/Ready.lean` completes the selected-input success criterion for both
  public variants without a separate packing-layout or global query-success
  premise. Missing/shared input stops omit packing queries. Entered node pairs
  require their actual factor/defaulted-depth results and selected arithmetic,
  geometry, and element calls; the results are recovered from execution,
  without positivity or power-of-two/coherence laws. Nonmutating rebase still
  requires its actual pending-map clone on every branch. Existing total success
  proofs now use this criterion. At `3231f6f` (foundations `d1ba797`, `4952ade`,
  `cb7e79e`), the full build passes (2,060 jobs), and the axiom/import audit
  covers 5,430 declarations across 344 modules. Seven additional declarations
  reuse the existing pointer contract, for 97 total. No new axiom or admission
  was introduced; `size_of` remains unused. Actual packing-helper outcomes,
  including the logarithm for packed factors, stay explicit conditions; no
  blanket query-totality or source-fidelity result is claimed. Packing and
  geometry for content/cache correctness, remaining assumption review,
  borrowed CoW, and model fidelity remain open. No Rust, extraction, external
  model, or Aeneas source changed; source suites and the 42-root/151-declaration
  model dependency gate were not repeated.
- The general public success criteria in `Rebase/SelectedConditions.lean`
  remove whole-tree shape and representable-layer assumptions. At a fixed
  packing layout, the selected arithmetic, binary geometry, and external
  element calls are jointly necessary and sufficient; nonmutating rebase
  additionally requires only the actual pending-map clone to return. The
  progressive input calculation preserves both machine clamps, and every
  metadata and recursive success is derived. Existing progressive/public
  success lemmas and total contracts now use the general proof through
  invariant adapters. At `2d63438` (foundations `15af31a`, `9e1c78c`, `9afa364`,
  `dfe9e73`), the full build passes (2,057 jobs), and the axiom/import audit
  covers 5,399 declarations across 341 modules. Nine additional declarations
  reuse the existing pointer contract, for 90 total; no new axiom or admission
  was introduced. This audits the selected success requirements at a fixed
  packing layout. Geometry for content/cache correctness, packing assumptions,
  remaining assumption review, and model fidelity stay open. No Rust,
  extraction, external model, or Aeneas source changed; source suites and the
  42-root/151-declaration model dependency gate were not repeated.
- Both public rebase success criteria are now equivalences. Under packing
  layout, compatible shapes, and representable original layers, in-place
  success requires exactly the selected element comparisons to terminate;
  nonmutating success also requires the actual pending-map clone to return.
  Binary/progressive reflection recovers these comparisons from successful
  calls, including final pointer reuse, without density, accurate lengths,
  semantic comparison/hash laws, or map-preservation laws. Binary reflection
  needs no geometry; progressive reflection needs only layout and original
  capacity. At `d5836d4` (foundations `3f2f4fa`, `c3ff39d`, `212ac40`), the full
  build passes (2,052 jobs), and the axiom/import audit covers 5,314 declarations
  across 336 modules. Of the 34 new declarations, 24 use only standard axioms
  or none, and ten reuse the existing pointer contract, for 81 dependent
  declarations total. No new axiom or admission was introduced. These are
  termination criteria under the stated geometry, superseded by the general
  selected-input criteria above. They do not establish source fidelity of
  external operations. Rust/extraction/models/Aeneas are unchanged, so neither source
  suites nor the 42-root/151-declaration dependency gate were repeated.
- Both public rebase cache criteria are now equivalences: under the existing
  semantic content laws and geometry, successful output validity holds
  exactly when retained-original and imported-base validity hold together.
  Binary and progressive reflection recover both laws from the actual output;
  the public proofs recover the actual clone/rebase calls without pending-map
  clone/read/maximum or representation laws. At `ad4e3f4` (foundations
  `0dc26d2`, `01b05f5`), the full build passes (2,048 jobs), and the axiom/import
  audit covers 5,280 declarations across 332 modules. All seven new operation
  lemmas reuse the existing pointer contract, bringing its dependent
  declaration count to 71. No new axiom or admission was introduced. This
  verifies the selected cache-validity premises under the stated content and
  geometry assumptions; remaining assumption and fidelity work stays open.
  Rust/extraction/models/Aeneas are unchanged, so neither source suites nor
  the 42-root/151-declaration dependency gate were repeated.
- `RebaseOrigCachesOn` scopes original validity to retained caches, while
  `RebaseHashCachesOn` separately covers reached nonzero hash-shortcut checks.
  Binary/progressive preservation uses the first; the collision bridges use
  the second. Eight successful-execution/total public cache contracts accept
  these weaker premises. Full original validity supplies both through
  adapters and is retained by the error-inclusive wrapper, whose error branch
  restores the original tree. Cleared-input contracts derive both scopes.
  The progressive step certificate retains completed child calls when final
  pointer checks reuse the original node. At `01f0d4f` (foundations `a653121`,
  `8173c77`), the full build passes (2,045 jobs), and the axiom/import audit
  covers 5,257 declarations across 329 modules. All 21 new scope declarations
  use only standard axioms or none. A pointer-equality helper adds one use of
  the existing pointer contract, for 64 total; no new axiom or admission was
  introduced. No Rust/extraction/model/Aeneas source changed, and neither the
  source suites nor the 42-root/151-declaration dependency gate were repeated.
- `RebaseBaseCachesOn` now selects base caches by the binary action category
  inside each reached progressive layer. No-ops require no base validity;
  whole-base replacement requires full base validity; rebuilding requires
  selected child-cache laws. Missing and shared progressive suffixes remain
  omitted, and full-base validity still supplies the scope. `KindReflection`
  proves the input classifier matches every successful extracted action at
  accurate dense metadata without element/cache soundness or termination
  laws. It retains the source's exact mixed-equality dispatch and is a proof
  artifact, not a replacement implementation. Binary/progressive preservation,
  both collision bridges, and all eleven public cache/validity contracts use
  the scope. At `99fad96` (foundation `b7e16e2`), the full build passes (2,041
  jobs), and the axiom/import audit covers 5,235 declarations across 325
  modules, with no new axioms or admissions. The reflection adds one use of
  the existing pointer contract, for 63 total. Rust/extraction/models are
  unchanged; neither source suites nor the 42-root/151-declaration dependency
  gate were repeated. The original-cache refinement is recorded above;
  remaining assumption and fidelity work stay open.
- Packed rebase equality now uses `NeSoundIfAllFalse`: element agreement is
  needed only when every paired `ne` returns false. The guarded law is proved
  necessary and sufficient for sound positive vector equality, conditional
  on matching lengths, and is implied by the earlier reached-pair law.
  One non-false paired result removes all soundness obligations for that
  vector, including earlier false answers. Every dependent public rebase
  contents/cache contract uses this weaker law; pointer/hash shortcuts and
  comparison termination laws retain their existing scope. At `fbf2a27`
  (foundation `e9ada7a`), focused and full builds pass (2,037 jobs), and the
  axiom/import audit validates 5,127 declarations across 321 modules. New
  results use only standard Lean axioms or none; the 62 existing pointer
  contract users are unchanged. This is an assumption audit, not additional
  Rust/model refinement. No Rust, extraction, external model, or Aeneas source
  changed; the dependency inventory remains 42 roots/151 local declarations,
  and its gate and the source-model suites were not repeated for this
  proof-only change.
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
