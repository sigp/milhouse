#!/usr/bin/env python3
"""Build and audit all Tree project theorems, including private/generated ones.

Run from any directory with Python 3. Reports and command logs are retained in
aeneas-lean/.lake/axiom-audit/. This checks kernel axiom dependencies and import
coverage; it does not establish Rust/model fidelity, API coverage, or minimality
of theorem hypotheses.
"""

import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# These two external contracts are explicitly documented in FunsExternal.lean.
MODEL_AXIOMS = {"triomphe.arc.Arc.ptr_eq_spec", "core.mem.size_of.usize_spec"}
EXTERNAL_TEMPLATES = {"Tree.FunsExternal_Template", "Tree.TypesExternal_Template"}


def validate(records, expected_modules):
    """Reject incomplete inventories and any unapproved axiom use/declaration."""
    summaries = [row for row in records if row.get("kind") == "summary"]
    if len(summaries) != 1:
        raise ValueError("Expected exactly one completed inventory summary")
    summary = summaries[0]
    modules = set(summary["modules"])
    if modules != expected_modules:
        raise ValueError(
            f"Module coverage mismatch: missing {sorted(expected_modules - modules)}; "
            f"unexpected {sorted(modules - expected_modules)}"
        )
    theorems = [row for row in records if row.get("kind") == "theorem"]
    axioms = [row for row in records if row.get("kind") == "axiom"]
    if len(records) != len(theorems) + len(axioms) + 1:
        raise ValueError("Unknown inventory record kind")
    if not theorems or len(theorems) != summary["theorems"]:
        raise ValueError("Theorem inventory is empty or truncated")
    if len(axioms) != summary["axiomDeclarations"]:
        raise ValueError("Axiom declaration inventory is truncated")
    declarations = theorems + axioms
    if len({row["name"] for row in declarations}) != len(declarations):
        raise ValueError("Duplicate declarations in inventory")
    if any(row["module"] not in modules for row in declarations):
        raise ValueError("A declaration belongs to an unreported module")
    failures = []
    for row in axioms:
        if row["name"] not in MODEL_AXIOMS:
            failures.append(f"{row['module']}: unexpected axiom declaration {row['name']}")
    allowed = STANDARD_AXIOMS | MODEL_AXIOMS
    for row in theorems:
        extra = set(row["axioms"]) - allowed
        if extra:
            failures.append(f"{row['name']}: unexpected dependencies {sorted(extra)}")
    if failures:
        raise ValueError("\n".join(failures))
    counts = Counter(ax for row in theorems for ax in set(row["axioms"]))
    return {
        "modules": sorted(modules),
        "theoremCount": len(theorems),
        "axiomDeclarations": sorted(row["name"] for row in axioms),
        "axiomUseCounts": dict(sorted(counts.items())),
        "theorems": sorted(theorems, key=lambda row: row["name"]),
    }


def main():
    project = Path(__file__).resolve().parents[1] / "aeneas-lean"
    output = project / ".lake" / "axiom-audit"
    output.mkdir(parents=True, exist_ok=True)
    report = output / "report.json"
    # A failed run must not leave an older successful report looking current.
    report.unlink(missing_ok=True)
    for command, log_name in [
        (["lake", "build"], "build.log"),
        (["lake", "env", "lean", "AuditAxioms.lean"], "inventory.jsonl"),
    ]:
        log = output / log_name
        print(f"Running {' '.join(command)}", flush=True)
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=project, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            print(f"Command failed with exit {result.returncode}; see {log}", file=sys.stderr)
            return 1
    expected = {"Tree"} | {
        ".".join(path.relative_to(project).with_suffix("").parts)
        for path in (project / "Tree").rglob("*.lean")
    }
    expected -= EXTERNAL_TEMPLATES
    inventory = (output / "inventory.jsonl").read_text()
    try:
        records = [json.loads(line) for line in inventory.splitlines() if line.strip()]
        result = validate(records, expected)
    except (ValueError, KeyError, TypeError) as error:
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        return 1
    report.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Axiom audit passed: {result['theoremCount']} theorem declarations, "
          f"{len(result['modules'])} project modules")
    print(f"Axiom use counts: {result['axiomUseCounts']}")
    print(f"Declared external axioms: {result['axiomDeclarations']}")
    print(f"Report: {report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
