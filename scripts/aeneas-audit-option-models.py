#!/usr/bin/env python3
"""Compare Option models with fresh, explicitly included core::option bodies."""

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


METHODS = (
    "is_some_and", "is_none_or", "map", "map_or", "unwrap_or_default",
    "ok_or", "or", "unzip", "copied", "branch", "from_residual",
)
PROOFS = tuple(f"option_{name}_agrees" for name in METHODS) + (
    "option_cloned_composition_agrees",
)
TOOLCHAIN = "nightly-2026-06-01"


def check_llbc(data):
    if data.get("has_errors") is not False or data.get("charon_version") != "0.1.223":
        raise ValueError("LLBC has errors or an unexpected Charon version")
    crate = data["translated"]
    if crate["crate_name"] != "option_source":
        raise ValueError("Unexpected source crate")
    files = {item["id"]: item for item in crate["files"] if item}
    verified = {}
    for name in METHODS:
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
                or source["name"] != {"Local": "/rustc/library/core/src/option.rs"}
                or not isinstance(item["body"], dict)
                or "Structured" not in item["body"]):
            raise ValueError(f"Missing transparent standard-library provenance for {name}")
        verified[name] = span
    return verified


def check_axiom_output(output):
    found = re.findall(r"'([^']+)' does not depend on any axioms", output)
    if len(found) != len(PROOFS) or set(found) != set(PROOFS):
        raise ValueError("Missing, duplicate, or unexpected axiom-free model checks")


def main():
    repo = Path(__file__).resolve().parent.parent
    lean_project = repo / "aeneas-lean"
    sources = lean_project / "reproducers/option_models"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", default=os.environ.get("CHARON", str(repo.parent / "aeneas/charon/bin/charon")))
    parser.add_argument("--aeneas", default=os.environ.get("AENEAS", str(repo.parent / "aeneas/bin/aeneas")))
    parser.add_argument("--output", type=Path, default=lean_project / ".lake/option-model-audit")
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
    command = [args.charon, "rustc", "--preset=aeneas", "--include", "core::option",
               "--dest-file", str(work / "option_source.llbc")]
    for name in METHODS:
        command += ["--start-from", "option_source::" + name]
    command += ["--", "--edition=2024", "--crate-type", "lib", "--crate-name",
                "option_source", str(sources / "source.rs")]
    run("charon", command, cwd=work)
    provenance = check_llbc(json.loads((work / "option_source.llbc").read_text()))
    run("aeneas", [args.aeneas, "-backend", "lean", "-namespace", "OptionSource",
                   "-split-files", "-no-progress-bar", "-dest", str(work / "OptionSource"),
                   str(work / "option_source.llbc")], cwd=work)
    generated = list((work / "OptionSource").glob("*.lean"))
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
    for module in ("OptionSource/Types", "OptionSource/Funs", "CheckModels"):
        output = run(module.replace("/", "-"), [lean, "-o", module + ".olean", module + ".lean"],
                     cwd=work, env=env)
        if module == "CheckModels":
            check_axiom_output(output)
    hashes = {str(path.relative_to(repo)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in (sources / "source.rs", sources / "CheckModels.lean",
                           lean_project / "Tree/FunsExternal.lean")}
    report.write_text(json.dumps({
        "versions": versions, "inputSha256": hashes, "runDirectory": str(work),
        "directSourceComparisons": provenance, "compositionChecks": ["cloned"],
        "unresolvedDirectExtraction": ["cloned"], "axiomFreeProofs": list(PROOFS),
        "limits": ["Aeneas reference/value abstraction", "destructor execution is not modeled"],
    }, indent=2) + "\n")
    print(f"Passed: {len(METHODS)} direct source comparisons and one cloned composition check; all axiom-free")
    print(f"Direct cloned extraction remains unresolved. Report: {report}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (KeyError, OSError, ValueError, RuntimeError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
