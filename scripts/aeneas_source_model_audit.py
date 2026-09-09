#!/usr/bin/env python3
"""Shared runner for comparisons with freshly extracted standard-library bodies."""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


TOOLCHAIN = "nightly-2026-06-01"


def check_llbc(data, suite):
    if data.get("has_errors") is not False or data.get("charon_version") != "0.1.223":
        raise ValueError("LLBC has errors or an unexpected Charon version")
    crate = data["translated"]
    if crate["crate_name"] != suite["crate"]:
        raise ValueError("Unexpected source crate")
    files = {item["id"]: item for item in crate["files"] if item}
    verified = {}
    for name in suite["source_files"]:
        candidates = [
            item for item in crate["fun_decls"] if item
            and item["item_meta"]["name"][0] == {"Ident": ["core", 0]}
            and item["item_meta"]["name"][-1] == {"Ident": [name, 0]}
        ]
        if len(candidates) != 1:
            raise ValueError(f"Expected one core body for {name}")
        item = candidates[0]
        meta = item["item_meta"]
        span = meta["span"]["data"]
        source = files[span["file_id"]]
        if (meta["is_local"] or meta["opacity"] != "Transparent"
                or source["crate_name"] != "core"
                or source["name"] != {"Local": suite["source_files"][name]}
                or not isinstance(item["body"], dict)
                or not isinstance(item["body"].get("Structured"), dict)):
            raise ValueError(f"Missing transparent standard-library provenance for {name}")
        verified[name] = span
    return verified


def check_axiom_output(output, proofs):
    records = re.findall(
        r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
        output,
    )
    if len(records) != len(proofs) or {name for name, _ in records} != set(proofs):
        raise ValueError("Missing, duplicate, or unexpected axiom reports")
    verified = {}
    for name, axioms in records:
        used = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
        if not used <= set(proofs[name]):
            raise ValueError(f"Unexpected axioms for {name}: {sorted(used)}")
        verified[name] = sorted(used)
    return verified


def main(suite):
    repo = Path(__file__).resolve().parent.parent
    lean_project = repo / "aeneas-lean"
    sources = lean_project / "reproducers" / suite["directory"]
    parser = argparse.ArgumentParser(description=suite["description"])
    parser.add_argument("--charon", default=os.environ.get("CHARON", str(repo.parent / "aeneas/charon/bin/charon")))
    parser.add_argument("--aeneas", default=os.environ.get("AENEAS", str(repo.parent / "aeneas/bin/aeneas")))
    parser.add_argument("--output", type=Path, default=lean_project / ".lake" / (suite["name"] + "-model-audit"))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = args.output / "report.json"
    report.unlink(missing_ok=True)
    work = Path(tempfile.mkdtemp(prefix="run-", dir=args.output.resolve()))

    def run(label, command, cwd=lean_project, env=None):
        print(f"Running {label}", flush=True)
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = work / (label + ".log")
        log.write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f"{label} failed ({result.returncode}); see {log}\n{result.stdout[-3000:]}")
        return result.stdout.strip()

    versions = {
        "charon": run("charon-version", [args.charon, "version"]),
        "aeneas": run("aeneas-version", [args.aeneas, "-version"]),
        "toolchain": run("charon-toolchain", [args.charon, "toolchain-version"]),
        "rustc": run("rustc-version", ["rustc", "+" + TOOLCHAIN, "--version", "--verbose"]),
    }
    if (versions["charon"] != "0.1.223" or versions["aeneas"] != "aeneas b59d5188"
            or versions["toolchain"] != TOOLCHAIN
            or "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65" not in versions["rustc"]):
        raise ValueError("Tool versions changed; review the source comparison before updating pins")
    run("build", ["lake", "build", "Tree.FunsExternal"])
    run("rustfmt", ["rustfmt", "+" + TOOLCHAIN, "--edition", "2024", "--check", str(sources / "source.rs")])
    run("native-build", ["rustc", "+" + TOOLCHAIN, "--edition", "2024", "--test",
                         str(sources / "source.rs"), "-o", str(work / "native")])
    run("native-tests", [str(work / "native")], cwd=work)
    command = [args.charon, "rustc", "--preset=aeneas"]
    for include in suite["includes"]:
        command += ["--include", include]
    llbc = work / (suite["crate"] + ".llbc")
    command += ["--dest-file", str(llbc)]
    for name in suite["source_files"]:
        command += ["--start-from", suite["crate"] + "::" + name]
    command += ["--", "--edition=2024", "--crate-type", "lib", "--crate-name",
                suite["crate"], str(sources / "source.rs")]
    run("charon", command, cwd=work)
    provenance = check_llbc(json.loads(llbc.read_text()), suite)
    run("aeneas", [args.aeneas, "-backend", "lean", "-namespace", suite["namespace"],
                   "-split-files", "-no-progress-bar", "-dest", str(work / suite["namespace"]),
                   str(llbc)], cwd=work)
    generated = list((work / suite["namespace"]).glob("*.lean"))
    if {path.name for path in generated} != {"Types.lean", "Funs.lean"}:
        raise ValueError("Unexpected generated files or external model templates")
    for path in generated:
        if re.search(r"\b(sorry|admit|axiom|opaque)\b", path.read_text()):
            raise ValueError(f"Incomplete or opaque generated body: {path}")
    env = os.environ.copy()
    base_path = run("lean-path", ["lake", "env", "printenv", "LEAN_PATH"])
    lean = run("lean-executable", ["lake", "env", "which", "lean"])
    env["LEAN_PATH"] = str(work) + os.pathsep + base_path
    shutil.copyfile(sources / "CheckModels.lean", work / "CheckModels.lean")
    for module in (suite["namespace"] + "/Types", suite["namespace"] + "/Funs", "CheckModels"):
        output = run(module.replace("/", "-"), [lean, "-o", module + ".olean", module + ".lean"],
                     cwd=work, env=env)
        if module == "CheckModels":
            checked_axioms = check_axiom_output(output, suite["proofs"])
    hashes = {str(path.relative_to(repo)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in (sources / "source.rs", sources / "CheckModels.lean",
                           lean_project / "Tree/FunsExternal.lean")}
    report.write_text(json.dumps({
        "versions": versions, "inputSha256": hashes, "runDirectory": str(work),
        "directSourceComparisons": provenance, "compositionChecks": suite["composition"],
        "unresolvedDirectExtraction": suite["unresolved"],
        "validatedProofs": checked_axioms,
        "axiomFreeProofs": [name for name, axioms in checked_axioms.items() if not axioms],
        "limits": ["Aeneas reference/value abstraction", "destructor execution is not modeled"],
    }, indent=2) + "\n")
    print(f"Passed: {len(suite['source_files'])} direct source comparisons and "
          f"{len(suite['composition'])} composition checks")
    print(f"Proofs: {len(checked_axioms)}; axiom-free: "
          f"{sum(not axioms for axioms in checked_axioms.values())}")
    if suite["unresolved"]:
        print("Unresolved direct extraction: " + ", ".join(suite["unresolved"]))
    print(f"Report: {report}")
    return 0


def run_suite(suite):
    try:
        return main(suite)
    except (KeyError, OSError, ValueError, RuntimeError) as error:
        print(error, file=sys.stderr)
        return 1
