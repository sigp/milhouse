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
