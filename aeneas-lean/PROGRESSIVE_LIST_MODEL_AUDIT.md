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
were not changed by this audit.

The BTreeMap lookup model occurs conservatively under `apply_updates` through
`utils.opt_hash`. That helper has an optional cached-hash map; a reference in
this inventory alone does not prove that the lookup executes. Similarly,
Arbitrary size-hint callers carry the full trait dictionary, so their closures
include generator definitions even though the default size-hint body returns
its fixed answer. Runtime reasoning still uses the existing branch proofs.

SSZ error formatting remains relevant to included decoder results even though
general Debug implementations are excluded. The specialized formatter's
string-buffer and default-option contract must not be extended to general
formatter options, user sinks, or lock observation without further work.

## Trusted boundaries and remaining work

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

Validation: the full library build passes (2,023 jobs), and the valid environment
inventory was accepted. Eight deliberately invalid inventories were rejected:
missing summary/root records, a summary preceding its roots, a duplicated
dependency, an unknown model module, a root outside the generated module, an
inserted reference to the excluded identity model, and a local model replacing
a milhouse implementation. Both external-source edits were checked to contain
only comments; no proof or model definition changed. The
separate [axiom/import audit](PROGRESSIVE_LIST_PROOFS.md#validation) remains
required for changes to proofs or model definitions.
