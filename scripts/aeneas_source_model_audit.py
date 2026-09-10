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

# This parameter represents one nondeterministic Bool outcome. The pinned
# power body queries the intrinsic once; both loops remain freshly extracted.
# Do not generalize this to callers that query it repeatedly: a constant
# outcome would then impose an invalid repeated-call consistency assumption.
POW_SELECTOR_SOURCE = """import Aeneas

open Aeneas Aeneas.Std Result

class PowSource.StaticKnown where
  outcome : Bool

def core.intrinsics.is_val_statically_known {T : Type} [PowSource.StaticKnown]
    (_markerCopyInst : core.marker.Copy T) (_value : T) : Result Bool :=
  ok PowSource.StaticKnown.outcome
"""

# Validate the call's control flow as well as its count. This is an expected
# shape, never a replacement for the freshly extracted function body.
POW_SELECTOR_CALLER = """
def core.num.Usize.pow
  (self : Std.Usize) (exp : Std.U32) : Result Std.Usize := do
  if exp = 0#u32
  then ok 1#usize
  else
    let b ← core.intrinsics.is_val_statically_known core.marker.CopyU32 exp
    if b
    then
      let (base, acc) ← core.num.Usize.pow_loop0 exp self 1#usize
      acc * base
    else core.num.Usize.pow_loop1 exp self 1#usize
"""


def prepare_pow_selector(data, template, original):
    """Validate the sole intrinsic boundary; add only a section parameter.

    The class is generated here, not populated from the admitted template.
    It has exactly one unconstrained Bool field and no axioms or instances.
    The comparison theorem quantifies over this class.
    """
    name = "core.intrinsics.is_val_statically_known"
    signature = "{T : Type} (markerCopyInst : core.marker.Copy T) : T → Result Bool"
    records = re.findall(r"(?m)^axiom ([A-Za-z_][\w.]*)[ \t]*\n((?:[^\n]+\n?)*)", template)
    if ([(n, " ".join(s.split())) for n, s in records] != [(name, signature)]
            or len(re.findall(r"(?m)^axiom\b", template)) != 1
            or re.search(r"\b(sorry|admit|opaque)\b", template)
            or re.search(r"(?m)^(def|theorem|abbrev|instance)\b", template)):
        raise ValueError("Unexpected power selector template")
    crate = data["translated"]
    source = source_declaration(crate, {"source_prefix": "core::intrinsics"},
                                "is_val_statically_known")
    meta = source["item_meta"]
    span = meta["span"]["data"]
    files = {file["id"]: file for file in crate["files"] if file}
    file = files[span["file_id"]]
    if (crate["crate_name"] != "pow_source" or meta["is_local"] is not False
            or meta["opacity"] != "Foreign" or source["is_global_initializer"] is not None
            or source["body"] != {"Intrinsic": {"name": "is_val_statically_known", "arg_names": ["_arg"]}}
            or file["crate_name"] != "core"
            or file["name"] != {"Local": "/rustc/library/core/src/intrinsics/mod.rs"}):
        raise ValueError("Unexpected power selector source provenance")
    # A single call in the non-loop power body is the only supported caller.
    start = original.find("\ndef core.num.Usize.pow\n")
    stop = original.find("\n/-- [pow_source::pow]", start)
    marker = "\nnamespace PowSource\n"
    parameter = "\nvariable [PowSource.StaticKnown]\n"
    if (start < 0 or stop < start or original.count(name) != 1
            or original[start:stop] != POW_SELECTOR_CALLER or original.count(marker) != 1
            or "PowSource.StaticKnown" in original):
        raise ValueError("Unexpected power selector call or parameter scope")
    prepared = original.replace(marker, marker + parameter, 1)
    if prepared.replace(marker + parameter, marker, 1) != original:
        raise ValueError("Power source body changed while introducing the selector parameter")
    record = {"method": "is_val_statically_known", "sourceCrate": "core",
              "sourceFile": "/rustc/library/core/src/intrinsics/mod.rs", "source": span,
              "defId": source["def_id"], "signature": signature,
              "parameter": "[PowSource.StaticKnown]", "outcomes": [False, True],
              "scope": "one intrinsic call per power invocation; both loops unchanged",
              "originalFunsSha256": hashlib.sha256(original.encode()).hexdigest(),
              "parameterizedFunsSha256": hashlib.sha256(prepared.encode()).hexdigest()}
    return prepared, record


def source_declaration(crate, suite, name, kind="fun_decls"):
    prefix_key = {"type_decls": "type_source_prefix", "trait_decls": "trait_source_prefix"}.get(
        kind, "source_prefix")
    module = suite.get(prefix_key, suite.get("source_crate", "core"))
    if kind == "fun_decls":
        module = suite.get("source_prefixes", {}).get(name, module)
    prefix = [{"Ident": [part, 0]} for part in module.split("::")]
    candidates = [item for item in crate[kind] if item
                  and item["item_meta"]["name"][:len(prefix)] == prefix
                  and item["item_meta"]["name"][-1] == {"Ident": [name, 0]}]
    if len(candidates) != 1:
        raise ValueError(f"Expected one dependency body for {name}")
    return candidates[0]


def trait_method_declaration(crate, suite, trait_name, method_name):
    trait = source_declaration(crate, suite, trait_name, "trait_decls")
    candidates = [(index, method) for index, method in enumerate(trait["methods"])
                  if method and method["skip_binder"]["name"] == method_name]
    if len(candidates) != 1:
        raise ValueError(f"Expected one source trait method: {trait_name}::{method_name}")
    index, method = candidates[0]
    return trait, index, method


def check_llbc(data, suite):
    if data.get("has_errors") is not False or data.get("charon_version") != "0.1.223":
        raise ValueError("LLBC has errors or an unexpected Charon version")
    crate = data["translated"]
    if crate["crate_name"] != suite["crate"]:
        raise ValueError("Unexpected source crate")
    source_crate = suite.get("source_crate", "core")
    source_crates = suite.get("source_crates", {})
    if set(source_crates) - set(suite["source_files"]):
        raise ValueError("Source-crate override has no selected source body")
    files = {item["id"]: item for item in crate["files"] if item}
    verified = {}
    for name in suite["source_files"]:
        item = source_declaration(crate, suite, name)
        meta = item["item_meta"]
        span = meta["span"]["data"]
        source = files[span["file_id"]]
        if (meta["is_local"] or meta["opacity"] != "Transparent"
                or source["crate_name"] != source_crates.get(name, source_crate)
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


def statement_nodes(value):
    """Find the exact pinned LLBC Statement schema, including nested blocks."""
    nodes = []
    if isinstance(value, dict):
        if set(value) == {"span", "id", "kind", "comments_before"}:
            nodes.append(value)
        for child in value.values():
            nodes.extend(statement_nodes(child))
    elif isinstance(value, list):
        for child in value:
            nodes.extend(statement_nodes(child))
    return nodes


def check_exclusions(original, selected, suite):
    """Compare complete declarations, optionally reconciling fresh statement IDs."""
    check_llbc(original, suite)
    check_llbc(selected, suite)
    renumberings = []
    for name in suite["source_files"]:
        before = source_declaration(original["translated"], suite, name)
        after = copy.deepcopy(source_declaration(selected["translated"], suite, name))
        if suite.get("allow_statement_renumbering"):
            old_nodes, new_nodes = statement_nodes(before["body"]), statement_nodes(after["body"])
            old_ids, new_ids = [s["id"] for s in old_nodes], [s["id"] for s in new_nodes]
            if (len(old_ids) != len(new_ids)
                    or any(type(i) is not int or i < 0 for i in old_ids + new_ids)
                    or len(set(old_ids)) != len(old_ids) or len(set(new_ids)) != len(new_ids)):
                raise ValueError(f"Invalid statement-ID correspondence: {name}")
            changes = []
            for old, new in zip(old_nodes, new_nodes):
                if old["id"] != new["id"]:
                    changes.append({"originalId": old["id"], "selectedId": new["id"]})
                new["id"] = old["id"]
            if changes:
                renumberings.append({"method": name, "statementIds": changes})
        if before != after:
            raise ValueError(f"Source declaration changed after exclusions: {name}")
    return list(suite["source_files"]), renumberings


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
    """Restore declared root/type/trait names, then validate all remaining LLBC."""
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
    methods = []
    seen = set()
    for change in suite.get("rename_trait_methods", []):
        trait_name, name, replacement = change["trait"], change["method"], change["replacement"]
        if (trait_name, name) in seen or not re.fullmatch(r"[A-Za-z_]\w*", replacement):
            raise ValueError("Invalid or duplicate source trait method rename")
        seen.add((trait_name, name))
        trait, index, method = trait_method_declaration(original["translated"], suite, trait_name, name)
        field = method["skip_binder"]
        for meta in (trait["item_meta"], field["item_meta"]):
            file = files[meta["span"]["data"]["file_id"]]
            if (meta["is_local"] is not False or meta["opacity"] != "Transparent"
                    or file["crate_name"] != suite.get("source_crate", "core")
                    or file["name"] != {"Local": change["source_file"]}):
                raise ValueError(f"Missing source trait/method provenance: {trait_name}::{name}")
        if (method["kind"] != {"TraitMethod": [trait["def_id"], index]}
                or field["item_meta"]["name"] != trait["item_meta"]["name"] + [{"Ident": [name, 0]}]
                or any(m and m["skip_binder"]["name"] == replacement for m in trait["methods"])):
            raise ValueError(f"Invalid or colliding source trait method: {trait_name}::{name}")
        renamed_trait, renamed_index, renamed_method = trait_method_declaration(
            restored["translated"], suite, trait_name, replacement)
        expected_name = trait["item_meta"]["name"] + [{"Ident": [replacement, 0]}]
        if (renamed_trait["def_id"] != trait["def_id"] or renamed_index != index
                or renamed_method["skip_binder"]["item_meta"]["name"] != expected_name):
            raise ValueError(f"Missing or incorrect trait method rename: {trait_name}::{name}")
        renamed_method["skip_binder"]["name"] = name
        renamed_method["skip_binder"]["item_meta"]["name"] = copy.deepcopy(field["item_meta"]["name"])
        methods.append({"trait": trait_name, "method": name, "extractedMethod": replacement,
                        "traitDefId": trait["def_id"], "methodId": index,
                        "source": field["item_meta"]["span"]["data"]})
    # This restores any separately declared function renames and compares the
    # entire result, including code, types, IDs, dictionaries, and source spans.
    renames = check_source_renames(original, restored, suite)
    return renames, retained, types, methods


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


def check_foundation_bindings(data, suite, template):
    """Allow listed dependency primitives supplied by existing concrete models.

    The template is inspected but never compiled. The replacement module may
    contain imports only; all generated source definitions stay untouched.
    """
    records = re.findall(r"(?m)^axiom ([A-Za-z_][\w.]*)[ \t]*\n((?:[^\n]+\n?)*)", template)
    bindings = suite.get("foundation_bindings", [])
    expected = {binding["lean_name"]: " ".join(binding["signature"].split()) for binding in bindings}
    if (len(expected) != len(bindings) or len(records) != len(expected)
            or len(re.findall(r"(?m)^axiom\b", template)) != len(records)
            or {name: " ".join(signature.split()) for name, signature in records} != expected
            or re.search(r"\b(sorry|admit|opaque)\b", template)
            or re.search(r"(?m)^(def|theorem|abbrev|instance)\b", template)):
        raise ValueError("Unexpected foundation template declarations or signatures")
    crate = data["translated"]
    files = {file["id"]: file for file in crate["files"] if file}
    verified = []
    for binding in bindings:
        module = binding["module"]
        if (not re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", module)
                or module not in suite.get("model_modules", [])
                or module.replace(".", "/") + ".lean" not in suite.get("model_files", [])):
            raise ValueError("Foundation import must be an explicit built and hashed model module")
        source = source_declaration(crate, {"source_prefix": binding["source_prefix"]}, binding["method"])
        meta = source["item_meta"]
        span = meta["span"]["data"]
        file = files[span["file_id"]]
        if (meta["is_local"] is not False or meta["opacity"] != "Foreign"
                or source["body"] != "Opaque" or source["is_global_initializer"] is not None
                or file["crate_name"] != binding["source_crate"]
                or file["name"] != {"Local": binding["source_file"]}):
            raise ValueError(f"Unexpected foundation source provenance: {binding['method']}")
        verified.append({"method": binding["method"], "sourceCrate": binding["source_crate"],
                         "sourceFile": binding["source_file"], "source": span, "defId": source["def_id"],
                         "leanName": binding["lean_name"], "module": module,
                         "signature": expected[binding["lean_name"]]})
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
    statement_renumberings = []
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
        unchanged, statement_renumberings = check_exclusions(original, selected, suite)
    renames = []
    retained = []
    type_renames = []
    method_renames = []
    if any(suite.get(key) for key in ("rename_sources", "retain_sources", "rename_source_types",
                                     "rename_trait_methods")):
        renamed = copy.deepcopy(selected)
        for name, replacement in suite.get("rename_sources", {}).items():
            source_declaration(renamed["translated"], suite, name)["item_meta"]["name"][-1] = {
                "Ident": [replacement, 0]}
        for name in suite.get("retain_sources", []):
            source_declaration(renamed["translated"], suite, name)["item_meta"]["is_local"] = True
        for name, replacement in suite.get("rename_source_types", {}).items():
            source_declaration(renamed["translated"], suite, name, "type_decls")["item_meta"]["name"][-1] = {
                "Ident": [replacement, 0]}
        for change in suite.get("rename_trait_methods", []):
            _, _, method = trait_method_declaration(renamed["translated"], suite,
                                                    change["trait"], change["method"])
            method["skip_binder"]["name"] = change["replacement"]
            method["skip_binder"]["item_meta"]["name"][-1] = {"Ident": [change["replacement"], 0]}
        original_name = "original-metadata.llbc" if (suite.get("retain_sources")
            or suite.get("rename_source_types") or suite.get("rename_trait_methods")) else "original-names.llbc"
        shutil.copyfile(llbc, work / original_name)
        llbc.write_text(json.dumps(renamed) + "\n")
        renames, retained, type_renames, method_renames = check_source_metadata(
            selected, json.loads(llbc.read_text()), suite)
    run("aeneas", [args.aeneas, "-backend", "lean", "-namespace", suite["namespace"],
                   "-split-files", "-no-progress-bar", "-dest", str(work / suite["namespace"]),
                   str(llbc)], cwd=work)
    generated = list((work / suite["namespace"]).glob("*.lean"))
    expected_generated = {"Types.lean", "Funs.lean"}
    if suite.get("foundation_bindings") or suite.get("pow_selector"):
        expected_generated.add("FunsExternal_Template.lean")
    if {path.name for path in generated} != expected_generated:
        raise ValueError("Unexpected generated files or external model templates")
    foundations = []
    selectors = []
    if suite.get("pow_selector"):
        if suite["namespace"] != "PowSource" or suite.get("foundation_bindings"):
            raise ValueError("Power selector requires its own comparison suite")
        funs = work / suite["namespace"] / "Funs.lean"
        original = funs.read_text()
        prepared, selector = prepare_pow_selector(selected,
            (work / suite["namespace"] / "FunsExternal_Template.lean").read_text(), original)
        (work / "Funs.original.lean").write_text(original)
        funs.write_text(prepared)
        selectors.append(selector)
        (work / suite["namespace"] / "Selector.lean").write_text(POW_SELECTOR_SOURCE)
        (work / suite["namespace"] / "FunsExternal.lean").write_text("import PowSource.Selector\n")
    if suite.get("foundation_bindings"):
        template_path = work / suite["namespace"] / "FunsExternal_Template.lean"
        foundations = check_foundation_bindings(selected, suite, template_path.read_text())
        # Import existing concrete definitions; no axiom or replacement source
        # body from the generated template is compiled or copied into this file.
        imports = list(dict.fromkeys(binding["module"] for binding in foundations))
        (work / suite["namespace"] / "FunsExternal.lean").write_text(
            "".join("import " + module + "\n" for module in imports))
    for path in generated:
        if (foundations or selectors) and path.name == "FunsExternal_Template.lean":
            continue
        if re.search(r"\b(sorry|admit|axiom|opaque)\b", path.read_text()):
            raise ValueError(f"Incomplete or opaque generated body: {path}")
    env = os.environ.copy()
    base_path = run("lean-path", ["lake", "env", "printenv", "LEAN_PATH"])
    lean = run("lean-executable", ["lake", "env", "which", "lean"])
    env["LEAN_PATH"] = str(work) + os.pathsep + base_path
    shutil.copyfile(sources / "CheckModels.lean", work / "CheckModels.lean")
    modules = [suite["namespace"] + "/Types"]
    if selectors:
        modules.append(suite["namespace"] + "/Selector")
    if foundations or selectors:
        modules.append(suite["namespace"] + "/FunsExternal")
    modules += [suite["namespace"] + "/Funs", "CheckModels"]
    for module in modules:
        output = run(module.replace("/", "-"), [lean, "-o", module + ".olean", module + ".lean"],
                     cwd=work, env=env)
        if module == "CheckModels":
            checked_axioms = check_axiom_output(output, suite["proofs"])
    inputs = [sources / "source.rs", sources / "CheckModels.lean"]
    inputs += [Path(__file__).resolve(), Path(sys.argv[0]).resolve()]
    inputs += [lean_project / path for path in suite.get("model_files", ["Tree/FunsExternal.lean"])]
    if cargo:
        inputs += [sources / "Cargo.toml", sources / "Cargo.lock"]
    hashes = {str(path.relative_to(repo)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs}
    report.write_text(json.dumps({
        "versions": versions, "inputSha256": hashes, "runDirectory": str(work),
        "dependencySources": dependency_sources,
        "excludedItems": exclusions, "unchangedSourceDeclarations": unchanged,
        "sourceStatementRenumberings": statement_renumberings,
        "sourceNameChanges": renames,
        "retainedSourceBodies": retained, "sourceTypeNameChanges": type_renames,
        "sourceTraitMethodNameChanges": method_renames,
        "retainedLocalFoundations": foundations,
        "abstractCompilerSelectors": selectors,
        "directSourceComparisons": {} if selectors else provenance,
        "parameterizedSourceComparisons": provenance if selectors else {},
        "compositionChecks": suite["composition"],
        "unresolvedDirectExtraction": suite["unresolved"],
        "validatedProofs": checked_axioms,
        "axiomFreeProofs": [name for name, axioms in checked_axioms.items() if not axioms],
        "limits": ["Aeneas reference/value abstraction", "destructor execution is not modeled"]
            + (["Compiler selector is an arbitrary total Bool; both outcomes are proved"]
               if selectors else []),
    }, indent=2) + "\n")
    print(f"Passed: {0 if selectors else len(provenance)} direct source comparisons, "
          f"{len(provenance) if selectors else 0} parameterized source comparisons and "
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
