#!/usr/bin/env python3
"""Shared runner for comparisons with freshly extracted dependency bodies."""

import argparse
import copy
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


def source_declaration(crate, suite, name, kind="fun_decls"):
    prefix = [{"Ident": [part, 0]} for part in
              suite.get("source_prefix", suite.get("source_crate", "core")).split("::")]
    candidates = [item for item in crate[kind] if item
                  and item["item_meta"]["name"][:len(prefix)] == prefix
                  and item["item_meta"]["name"][-1] == {"Ident": [name, 0]}]
    if len(candidates) != 1:
        raise ValueError(f"Expected one dependency body for {name}")
    return candidates[0]


def check_llbc(data, suite):
    if data.get("has_errors") is not False or data.get("charon_version") != "0.1.223":
        raise ValueError("LLBC has errors or an unexpected Charon version")
    crate = data["translated"]
    if crate["crate_name"] != suite["crate"]:
        raise ValueError("Unexpected source crate")
    source_crate = suite.get("source_crate", "core")
    files = {item["id"]: item for item in crate["files"] if item}
    verified = {}
    for name in suite["source_files"]:
        item = source_declaration(crate, suite, name)
        meta = item["item_meta"]
        span = meta["span"]["data"]
        source = files[span["file_id"]]
        if (meta["is_local"] or meta["opacity"] != "Transparent"
                or source["crate_name"] != source_crate
                or source["name"] != {"Local": suite["source_files"][name]}
                or not isinstance(item["body"], dict)
                or not isinstance(item["body"].get("Structured"), dict)):
            raise ValueError(f"Missing transparent dependency provenance for {name}")
        initializer = item["is_global_initializer"]
        if name in suite.get("initializers", []):
            globals_ = [g for g in crate["global_decls"] if g
                        and type(initializer) is int and g["def_id"] == initializer]
            if len(globals_) != 1:
                raise ValueError(f"Missing global declaration for {name}")
            global_ = globals_[0]
            call = global_["value"]["kind"].get("Call")
            if (global_["item_meta"] != meta or global_["global_kind"] != "NamedConst"
                    or not isinstance(call, list) or len(call) != 2
                    or call[0]["kind"] != {"Fun": {"Regular": item["def_id"]}}
                    or call[1] != []):
                raise ValueError(f"Mismatched constant initializer for {name}")
        elif initializer is not None:
            raise ValueError(f"Unexpected global initializer for {name}")
        verified[name] = span
    return verified


def check_exclusions(original, selected, suite):
    """Require source declarations to remain identical when omitting unused items."""
    check_llbc(original, suite)
    check_llbc(selected, suite)
    for name in suite["source_files"]:
        if (source_declaration(original["translated"], suite, name)
                != source_declaration(selected["translated"], suite, name)):
            raise ValueError(f"Source declaration changed after exclusions: {name}")
    return list(suite["source_files"])


def check_source_renames(original, renamed, suite):
    """Allow only declared final-name changes; compare the entire restored LLBC."""
    check_llbc(original, suite)
    restored = copy.deepcopy(renamed)
    records = []
    for name, replacement in suite.get("rename_sources", {}).items():
        if name not in suite["source_files"] or not re.fullmatch(r"[A-Za-z_]\w*", replacement):
            raise ValueError("Invalid source rename")
        source = source_declaration(original["translated"], suite, name)
        expected_name = copy.deepcopy(source["item_meta"]["name"])
        expected_name[-1] = {"Ident": [replacement, 0]}
        if any(f and f["item_meta"]["name"] == expected_name
               for f in original["translated"]["fun_decls"]):
            raise ValueError(f"Source rename collides with an existing declaration: {name}")
        candidates = [f for f in restored["translated"]["fun_decls"] if f
                      and f["def_id"] == source["def_id"]]
        if len(candidates) != 1 or candidates[0]["item_meta"]["name"] != expected_name:
            raise ValueError(f"Missing or incorrect source rename: {name}")
        if sum(bool(f and f["item_meta"]["name"] == expected_name)
               for f in renamed["translated"]["fun_decls"]) != 1:
            raise ValueError(f"Ambiguous source rename: {name}")
        candidates[0]["item_meta"]["name"] = copy.deepcopy(source["item_meta"]["name"])
        records.append({"method": name, "extractedMethod": replacement, "defId": source["def_id"]})
    if restored != original:
        raise ValueError("LLBC changed beyond the declared source names")
    return records


def check_source_metadata(original, adjusted, suite):
    """Restore declared root/type metadata, then validate all remaining LLBC."""
    check_llbc(original, suite)
    restored = copy.deepcopy(adjusted)
    retained = []
    names = suite.get("retain_sources", [])
    if len(set(names)) != len(names):
        raise ValueError("Duplicate retained source body")
    for name in names:
        if name not in suite["source_files"] or name in suite.get("initializers", []):
            raise ValueError("Invalid retained source body")
        source = source_declaration(original["translated"], suite, name)
        candidates = [f for f in restored["translated"]["fun_decls"] if f
                      and f["def_id"] == source["def_id"]]
        if (source["item_meta"]["is_local"] is not False or len(candidates) != 1
                or candidates[0]["item_meta"]["is_local"] is not True):
            raise ValueError(f"Missing or incorrect source retention: {name}")
        candidates[0]["item_meta"]["is_local"] = False
        retained.append({"method": name, "defId": source["def_id"]})
    types = []
    files = {f["id"]: f for f in original["translated"]["files"] if f}
    for name, replacement in suite.get("rename_source_types", {}).items():
        if (name not in suite.get("type_source_files", {})
                or not re.fullmatch(r"[A-Za-z_]\w*", replacement)):
            raise ValueError("Invalid source type rename")
        source = source_declaration(original["translated"], suite, name, "type_decls")
        meta = source["item_meta"]
        span = meta["span"]["data"]
        file = files[span["file_id"]]
        if (meta["is_local"] is not False or meta["opacity"] != "Transparent"
                or file["crate_name"] != suite.get("source_crate", "core")
                or file["name"] != {"Local": suite["type_source_files"][name]}
                or not isinstance(source["kind"], dict)):
            raise ValueError(f"Missing source type provenance: {name}")
        expected_name = copy.deepcopy(meta["name"])
        expected_name[-1] = {"Ident": [replacement, 0]}
        if any(t and t["item_meta"]["name"] == expected_name
               for t in original["translated"]["type_decls"]):
            raise ValueError(f"Source type rename collides: {name}")
        candidates = [t for t in restored["translated"]["type_decls"] if t
                      and t["def_id"] == source["def_id"]]
        if (len(candidates) != 1 or candidates[0]["item_meta"]["name"] != expected_name
                or sum(bool(t and t["item_meta"]["name"] == expected_name)
                       for t in adjusted["translated"]["type_decls"]) != 1):
            raise ValueError(f"Missing or incorrect source type rename: {name}")
        candidates[0]["item_meta"]["name"] = copy.deepcopy(meta["name"])
        types.append({"type": name, "extractedType": replacement,
                      "defId": source["def_id"], "source": span})
    # This restores any separately declared function renames and compares the
    # entire result, including code, types, IDs, dictionaries, and source spans.
    renames = check_source_renames(original, restored, suite)
    return renames, retained, types


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
    dependency_sources = []
    cargo = suite.get("cargo_dependency")
    if cargo:
        metadata = json.loads(run("cargo-metadata", ["cargo", "+" + TOOLCHAIN,
            "metadata", "--offline", "--locked", "--format-version", "1",
            "--manifest-path", str(sources / "Cargo.toml")]))
        packages = [p for p in metadata["packages"] if p["name"] == cargo["name"]]
        if (len(packages) != 1 or packages[0]["version"] != cargo["version"]
                or packages[0]["source"] != "registry+https://github.com/rust-lang/crates.io-index"):
            raise ValueError("Unexpected dependency package/version/source")
        package = packages[0]
        for relative in cargo["files"]:
            path = Path(package["manifest_path"]).parent / relative
            dependency_sources.append({"package": cargo["name"], "version": cargo["version"],
                "file": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    run("build", ["lake", "build", *suite.get("model_modules", ["Tree.FunsExternal"])])
    run("rustfmt", ["rustfmt", "+" + TOOLCHAIN, "--edition", "2024", "--check", str(sources / "source.rs")])
    if cargo:
        run("native-tests", ["cargo", "+" + TOOLCHAIN, "test", "--offline", "--locked",
            "--lib", "--manifest-path", str(sources / "Cargo.toml")])
    else:
        run("native-build", ["rustc", "+" + TOOLCHAIN, "--edition", "2024", "--test",
                             str(sources / "source.rs"), "-o", str(work / "native")])
        run("native-tests", [str(work / "native")], cwd=work)
    command = [args.charon, "cargo" if cargo else "rustc", "--preset=aeneas"]
    if suite.get("excludes"):
        # Compare complete source declarations, not references to separately
        # serialized hash-consed values whose meaning could change between runs.
        command += ["--no-dedup-serialized-ast"]
    for include in suite["includes"]:
        command += ["--include", include]
    llbc = work / (suite["crate"] + ".llbc")
    command += ["--dest-file", str(llbc)]
    for name in suite.get("roots", suite["source_files"]):
        command += ["--start-from", suite["crate"] + "::" + name]
    for name in suite.get("dependency_roots", []):
        command += ["--start-from", name]
    if cargo:
        command += ["--", "--offline", "--locked", "--manifest-path", str(sources / "Cargo.toml")]
    else:
        command += ["--", "--edition=2024", "--crate-type", "lib", "--crate-name",
                    suite["crate"], str(sources / "source.rs")]
    exclusions = suite.get("excludes", [])
    unchanged = []
    if exclusions:
        run("charon-unfiltered", command, cwd=work)
        original = json.loads(llbc.read_text())
        shutil.copyfile(llbc, work / "unfiltered.llbc")
        position = command.index("--")
        command[position:position] = [part for name in exclusions for part in ("--exclude", name)]
    run("charon", command, cwd=work)
    selected = json.loads(llbc.read_text())
    provenance = check_llbc(selected, suite)
    if exclusions:
        unchanged = check_exclusions(original, selected, suite)
    renames = []
    retained = []
    type_renames = []
    if any(suite.get(key) for key in ("rename_sources", "retain_sources", "rename_source_types")):
        renamed = copy.deepcopy(selected)
        for name, replacement in suite.get("rename_sources", {}).items():
            source_declaration(renamed["translated"], suite, name)["item_meta"]["name"][-1] = {
                "Ident": [replacement, 0]}
        for name in suite.get("retain_sources", []):
            source_declaration(renamed["translated"], suite, name)["item_meta"]["is_local"] = True
        for name, replacement in suite.get("rename_source_types", {}).items():
            source_declaration(renamed["translated"], suite, name, "type_decls")["item_meta"]["name"][-1] = {
                "Ident": [replacement, 0]}
        original_name = "original-metadata.llbc" if (suite.get("retain_sources")
            or suite.get("rename_source_types")) else "original-names.llbc"
        shutil.copyfile(llbc, work / original_name)
        llbc.write_text(json.dumps(renamed) + "\n")
        renames, retained, type_renames = check_source_metadata(selected, json.loads(llbc.read_text()), suite)
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
    inputs = [sources / "source.rs", sources / "CheckModels.lean"]
    inputs += [lean_project / path for path in suite.get("model_files", ["Tree/FunsExternal.lean"])]
    if cargo:
        inputs += [sources / "Cargo.toml", sources / "Cargo.lock"]
    hashes = {str(path.relative_to(repo)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs}
    report.write_text(json.dumps({
        "versions": versions, "inputSha256": hashes, "runDirectory": str(work),
        "dependencySources": dependency_sources,
        "excludedItems": exclusions, "unchangedSourceDeclarations": unchanged,
        "sourceNameChanges": renames,
        "retainedSourceBodies": retained, "sourceTypeNameChanges": type_renames,
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
