#!/usr/bin/env python3
"""Build and inventory local model dependencies of available ProgressiveList APIs.

This is a conservative definition-body closure, not a call graph or a proof of
model fidelity. Generic callbacks are unresolved and complete trait dictionaries
can contribute unused fields. See PROGRESSIVE_LIST_MODEL_AUDIT.md.
"""

import hashlib
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


INHERENT = {
    "empty", "new", "try_from_iter", "get", "get_mut", "get_cow", "push", "len",
    "is_empty", "has_pending_updates", "apply_updates", "iter", "iter_from",
    "iter_cow", "iter_cow_from", "to_vec", "pop_front", "rebase", "rebase_on",
}
OTHER_LABELS = {
    "Default", "TryFromVec", "TryFromIter", "IntoIterator", "Clone", "CloneFrom",
    "PartialEq", "Iterator.next", "Iterator.size_hint", "Iterator.len", "Cow.into_mut",
    "Encode.is_ssz_fixed_len", "Encode.ssz_fixed_len", "Encode.ssz_bytes_len",
    "Encode.ssz_append", "Encode.as_ssz_bytes", "Decode.is_ssz_fixed_len",
    "Decode.ssz_fixed_len", "Decode.from_ssz_bytes", "Arbitrary.arbitrary",
    "arbitrary_take_rest", "arbitrary_size_hint", "arbitrary_try_size_hint",
}
MODEL_MODULES = {
    "Tree.TypesExternal", "Tree.FunsExternal", "Tree.Cow.EntryModels",
    "Tree.Ssz.Models", "Tree.Ssz.DecodeModels", "Tree.Formatting.Models",
    "Tree.Arbitrary.Models",
}
GENERATED_MODULES = {"Tree.Funs", "Tree.Types"}
# These are outside the revised goal and must not underpin its included APIs.
FORBIDDEN_PREFIXES = (
    "milhouse.list.List.intra_rebase",
    "std.collections.hash.map.HashMap.",
    "std.hash.random.",
    "lock_api.rwlock.RwLock.write",
    "lock_api.rwlock.RwLock.Insts.CoreFmtDebug.fmt",
    "alloy_primitives.bits.fixed.FixedBytes.Insts.CoreFmtDebug.fmt",
)
MILHOUSE_IMPLEMENTATION_PREFIXES = (
    "milhouse.progressive_list.", "milhouse.progressive_tree.", "milhouse.tree.",
    "milhouse.builder.", "milhouse.packed_leaf.", "milhouse.cow.", "milhouse.list.",
)


def validate(manifest, records):
    labels = [row["label"] for row in manifest]
    declarations = [row["declaration"] for row in manifest]
    if set(labels) != INHERENT | OTHER_LABELS or len(set(labels)) != len(labels):
        raise ValueError("Root labels differ from the available API inventory")
    if len(set(declarations)) != len(declarations):
        raise ValueError("Duplicate root declaration")
    for row in manifest:
        if row["label"] in INHERENT:
            expected = "milhouse.progressive_list.ProgressiveList." + row["label"]
            if row["declaration"] != expected:
                raise ValueError(f"Incorrect inherent root: {row['label']}")
    summaries = [row for row in records if row.get("kind") == "summary"]
    roots = [row for row in records if row.get("kind") == "root"]
    if len(summaries) != 1 or summaries[0]["roots"] != len(manifest):
        raise ValueError("Missing or incomplete final summary")
    if records[-1] is not summaries[0]:
        raise ValueError("Summary must be the final record")
    if len(records) != len(roots) + 1 or len(roots) != len(manifest):
        raise ValueError("Unexpected records or incomplete root inventory")
    if [(r["label"], r["declaration"]) for r in roots] != [
        (r["label"], r["declaration"]) for r in manifest
    ]:
        raise ValueError("Output roots differ from the manifest")
    models = {}
    forbidden = []
    for root in roots:
        nodes = root["nodes"]
        names = [n["name"] for n in nodes]
        if len(set(names)) != len(names):
            raise ValueError(f"Duplicate dependency under {root['label']}")
        matches = [n for n in nodes if n["name"] == root["declaration"]]
        if (len(matches) != 1 or matches[0]["kind"] != "definition"
                or matches[0]["module"] != "Tree.Funs"):
            raise ValueError(f"Root definition absent under {root['label']}")
        for node in nodes:
            if node["kind"] not in {"definition", "opaque", "axiom", "theorem", "type"}:
                raise ValueError(f"Unknown declaration kind: {node}")
            if node["name"].startswith(FORBIDDEN_PREFIXES):
                forbidden.append(f"{root['label']}: {node['name']}")
            if node["module"] not in GENERATED_MODULES:
                if node["name"].startswith(MILHOUSE_IMPLEMENTATION_PREFIXES):
                    raise ValueError(f"Milhouse implementation replaced by a local model: {node['name']}")
                if node["module"] not in MODEL_MODULES:
                    raise ValueError(f"Unreviewed local dependency module: {node['module']}")
                if node["name"] in models and models[node["name"]] != node:
                    raise ValueError(f"Inconsistent dependency record: {node['name']}")
                models[node["name"]] = node
        root["nodes"] = sorted(nodes, key=lambda n: n["name"])
    if forbidden:
        raise ValueError("Excluded model references:\n" + "\n".join(forbidden))
    return {
        "rootCount": len(roots),
        "localModelDeclarations": sorted(models.values(), key=lambda n: n["name"]),
        "localModelModuleCounts": dict(sorted(Counter(n["module"] for n in models.values()).items())),
        "roots": roots,
    }


def source_assumptions(policy, inventory):
    """Expose the single approved source-fidelity exception and its callers.

    This does not approve Lean axioms or alter the definition/import checks.
    Any further source exception requires an explicit policy/checker change.
    """
    if not isinstance(policy, dict) or set(policy) != {"version", "assumptions"} or policy["version"] != 1:
        raise ValueError("Unexpected source-assumption policy format")
    entries = policy["assumptions"]
    if not isinstance(entries, list) or len(entries) != 1:
        raise ValueError("Expected only the approved usize::pow source assumption")
    entry = entries[0]
    expected = {
        "rustItem": "core::num::{usize}::pow", "leanDeclaration": "core.num.Usize.pow",
        "modelModule": "Tree.FunsExternal", "modelFile": "Tree/FunsExternal.lean",
        "status": "assumed", "approvedOn": "2026-09-11",
        "deferredCheck": "core_pow_agrees in reproducers/pow_models/CheckModels.lean",
    }
    if (not isinstance(entry, dict) or set(entry) != set(expected) | {"reason", "contract"}
            or any(entry[key] != value for key, value in expected.items())
            or any(not isinstance(entry[key], str) or not entry[key].strip() for key in ["reason", "contract"])):
        raise ValueError("Unexpected source assumption; only usize::pow is approved")
    declaration = {"kind": "definition", "module": entry["modelModule"], "name": entry["leanDeclaration"]}
    matches = [node for node in inventory["localModelDeclarations"] if node["name"] == entry["leanDeclaration"]]
    if matches != [declaration]:
        raise ValueError("The assumed pow model must remain an inventoried concrete definition")
    roots = sorted(root["label"] for root in inventory["roots"]
                   if any(node["name"] == entry["leanDeclaration"] for node in root["nodes"]))
    if not roots:
        raise ValueError("The assumed pow model is absent from the root inventory")
    return [{**entry, "conservativeDependentRoots": roots}]


def main():
    project = Path(__file__).resolve().parents[1] / "aeneas-lean"
    output = project / ".lake" / "model-audit"
    output.mkdir(parents=True, exist_ok=True)
    report = output / "report.json"
    report.unlink(missing_ok=True)
    try:
        manifest = json.loads((project / "PROGRESSIVE_LIST_MODEL_ROOTS.json").read_text())
        for command, log_name in [
            (["lake", "build"], "build.log"),
            (["lake", "env", "lean", "AuditProgressiveListModels.lean"], "inventory.jsonl"),
        ]:
            log = output / log_name
            print(f"Running {' '.join(command)}", flush=True)
            with log.open("w") as stream:
                result = subprocess.run(command, cwd=project, stdout=stream, stderr=subprocess.STDOUT)
            if result.returncode:
                print(f"Command failed with exit {result.returncode}; see {log}", file=sys.stderr)
                return 1
        records = [json.loads(line) for line in (output / "inventory.jsonl").read_text().splitlines() if line.strip()]
        result = validate(manifest, records)
        policy_path = project / "SOURCE_MODEL_ASSUMPTIONS.json"
        result["assumedRustModels"] = source_assumptions(json.loads(policy_path.read_text()), result)
        result["sourceAssumptionPolicySha256"] = hashlib.sha256(policy_path.read_bytes()).hexdigest()
        for entry in result["assumedRustModels"]:
            entry["modelFileSha256"] = hashlib.sha256((project / entry["modelFile"]).read_bytes()).hexdigest()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Model dependency audit failed: {error}", file=sys.stderr)
        return 1
    report.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Model dependency audit passed: {result['rootCount']} roots, "
          f"{len(result['localModelDeclarations'])} local model declarations")
    print(f"Local model module counts: {result['localModelModuleCounts']}")
    print("Assumed Rust/model correspondence (not proved): " +
          ", ".join(entry["rustItem"] for entry in result["assumedRustModels"]))
    print(f"Report: {report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
