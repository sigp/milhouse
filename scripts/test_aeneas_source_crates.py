"""Check mixed dependency provenance without weakening the original crate gate."""

import copy
import unittest

from aeneas_source_model_audit import check_exclusions, check_foundation_bindings, check_llbc


class SourceCrateTests(unittest.TestCase):
    def setUp(self):
        self.suite = {
            "crate": "vec_map_source", "source_crate": "vec_map",
            "source_crates": {"as_ref": "core"},
            "source_prefixes": {"as_ref": "core::option"},
            "source_files": {"get": "/vec_map/src/lib.rs", "as_ref": "/core/src/option.rs"},
        }
        declarations = []
        for index, parts in enumerate([("vec_map", "get"), ("core", "option", "as_ref")]):
            declarations.append({
                "def_id": index, "src": "Normal",
                "body": {"Structured": {}},
                "item_meta": {
                    "name": [{"Ident": [part, 0]} for part in parts],
                    "span": {"Untagged": {"data": {"file_id": index}, "generated_from_span": None}},
                    "is_local": False, "opacity": "Transparent",
                },
            })
        self.data = {
            "has_errors": False, "charon_version": "0.1.251",
            "translated": {
                "crate_name": "vec_map_source", "fun_decls": declarations,
                "files": [
                    {"id": 0, "crate_name": "vec_map", "name": {"Local": "/vec_map/src/lib.rs"}},
                    {"id": 1, "crate_name": "core", "name": {"Local": "/core/src/option.rs"}},
                ],
            },
        }

    def test_accepts_expected_crate_for_each_selected_body_without_mutation(self):
        before = copy.deepcopy(self.data)
        self.assertEqual(set(check_llbc(self.data, self.suite)), {"get", "as_ref"})
        self.assertEqual(self.data, before)

    def test_legacy_single_crate_validation_is_unchanged(self):
        suite = {k: v for k, v in self.suite.items() if k not in {"source_crates", "source_prefixes"}}
        suite["source_files"] = {"get": "/vec_map/src/lib.rs"}
        self.assertEqual(set(check_llbc(self.data, suite)), {"get"})
        data = copy.deepcopy(self.data)
        data["translated"]["files"][0]["crate_name"] = "core"
        with self.assertRaisesRegex(ValueError, "provenance"):
            check_llbc(data, suite)

    def test_rejects_wrong_crate_path_body_or_transparency_for_either_dependency(self):
        for index in [0, 1]:
            for field in ["crate", "path", "body", "opacity", "local"]:
                data = copy.deepcopy(self.data)
                source = data["translated"]["files"][index]
                declaration = data["translated"]["fun_decls"][index]
                if field == "crate":
                    source["crate_name"] = "vec_map" if index else "core"
                elif field == "path":
                    source["name"] = {"Local": "/substitute.rs"}
                elif field == "body":
                    declaration["body"] = "Opaque"
                elif field == "opacity":
                    declaration["item_meta"]["opacity"] = "Foreign"
                else:
                    declaration["item_meta"]["is_local"] = True
                with self.subTest(index=index, field=field), self.assertRaisesRegex(ValueError, "provenance"):
                    check_llbc(data, self.suite)

    def test_rejects_unselected_crate_override(self):
        suite = copy.deepcopy(self.suite)
        suite["source_crates"]["unused"] = "core"
        with self.assertRaisesRegex(ValueError, "no selected source body"):
            check_llbc(self.data, suite)

    def test_rejects_old_compiler_and_unsupported_span_formats(self):
        data = copy.deepcopy(self.data)
        data["charon_version"] = "0.1.223"
        with self.assertRaisesRegex(ValueError, "version"):
            check_llbc(data, self.suite)
        for span in [{"data": {"file_id": 0}}, {"Tagged": {"data": {"file_id": 0}}}]:
            data = copy.deepcopy(self.data)
            data["translated"]["fun_decls"][0]["item_meta"]["span"] = span
            with self.subTest(span=span), self.assertRaisesRegex(ValueError, "source span"):
                check_llbc(data, self.suite)

    def test_global_initializer_must_link_to_the_selected_body(self):
        suite = copy.deepcopy(self.suite)
        suite["initializers"] = ["get"]
        data = copy.deepcopy(self.data)
        function = data["translated"]["fun_decls"][0]
        function["src"] = {"GlobalInitializer": {"id": 7, "generics": {}}}
        global_ = {"def_id": 7, "item_meta": copy.deepcopy(function["item_meta"]),
                   "global_kind": "NamedConst", "value": {"Untagged": [
                       {"Call": [{"kind": {"Fun": {"Regular": 0}}}, []]}, "type"]}}
        data["translated"]["global_decls"] = [global_]
        self.assertEqual(set(check_llbc(data, suite)), {"get", "as_ref"})
        for change in ["global_id", "callee", "arguments", "metadata", "kind", "expression"]:
            bad = copy.deepcopy(data)
            g = bad["translated"]["global_decls"][0]
            if change == "global_id":
                g["def_id"] = 8
            elif change == "callee":
                g["value"]["Untagged"][0]["Call"][0]["kind"]["Fun"]["Regular"] = 1
            elif change == "arguments":
                g["value"]["Untagged"][0]["Call"][1] = [0]
            elif change == "metadata":
                g["item_meta"]["is_local"] = True
            elif change == "kind":
                g["global_kind"] = "Static"
            else:
                g["value"] = {"Untagged": [{"Literal": 0}, "type"]}
            with self.subTest(change=change), self.assertRaises(ValueError):
                check_llbc(bad, suite)
        with self.assertRaisesRegex(ValueError, "Unexpected global initializer"):
            check_llbc(data, self.suite)

    def test_exclusion_allows_only_bijective_statement_and_block_renumbering(self):
        suite = copy.deepcopy(self.suite)
        suite["allow_statement_renumbering"] = True
        original = copy.deepcopy(self.data)
        block = {"span": {}, "id": 0, "statements": [
            {"span": {}, "id": 0, "kind": "Return", "comments_before": []},
            {"span": {}, "id": 1, "kind": "Nop", "comments_before": []}]}
        original["translated"]["fun_decls"][0]["body"] = {"Structured": {"body": block}}
        selected = copy.deepcopy(original)
        renamed = selected["translated"]["fun_decls"][0]["body"]["Structured"]["body"]
        renamed["id"] = 10
        for index, statement in enumerate(renamed["statements"]):
            statement["id"] = index + 20
        before = copy.deepcopy(selected)
        unchanged, records = check_exclusions(original, selected, suite)
        self.assertEqual(unchanged, ["get", "as_ref"])
        self.assertEqual(records, [{"method": "get", "statementIds": [
            {"originalId": 0, "selectedId": 20}, {"originalId": 1, "selectedId": 21}],
            "blockIds": [{"originalId": 0, "selectedId": 10}]}])
        self.assertEqual(selected, before)
        for change in ["operation", "span", "duplicate_id", "negative_id", "bool_id", "count"]:
            bad = copy.deepcopy(selected)
            body = bad["translated"]["fun_decls"][0]["body"]["Structured"]["body"]
            if change == "operation":
                body["statements"][0]["kind"] = "Abort"
            elif change == "span":
                body["span"] = {"different": True}
            elif change == "duplicate_id":
                body["statements"][1]["id"] = 20
            elif change == "negative_id":
                body["id"] = -1
            elif change == "bool_id":
                body["id"] = True
            else:
                body["statements"].pop()
            with self.subTest(change=change), self.assertRaises(ValueError):
                check_exclusions(original, bad, suite)

    def test_intrinsic_foundation_requires_exact_body_provenance_and_signature(self):
        data = copy.deepcopy(self.data)
        source = data["translated"]["fun_decls"][0]
        source["body"] = {"Intrinsic": {"name": "assume", "arg_names": ["b"]}}
        source["item_meta"]["opacity"] = "Foreign"
        suite = {"model_modules": ["Tree.Intrinsics"], "model_files": ["Tree/Intrinsics.lean"],
                 "foundation_bindings": [{"method": "get", "source_prefix": "vec_map",
                     "source_crate": "vec_map", "source_file": "/vec_map/src/lib.rs",
                     "lean_name": "core.intrinsics.assume", "signature": ": Bool → Result Unit",
                     "intrinsic": {"name": "assume", "arg_names": ["b"]},
                     "module": "Tree.Intrinsics"}]}
        template = "axiom core.intrinsics.assume : Bool → Result Unit\n"
        self.assertEqual(len(check_foundation_bindings(data, suite, template)), 1)
        for body in ["Opaque", {"Intrinsic": {"name": "other", "arg_names": ["b"]}},
                     {"Intrinsic": {"name": "assume", "arg_names": []}}, {"Structured": {}}]:
            bad = copy.deepcopy(data)
            bad["translated"]["fun_decls"][0]["body"] = body
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, "provenance"):
                check_foundation_bindings(bad, suite, template)
        for bad_template in [template.replace("Bool", "Nat"), template + "axiom extra : Nat\n"]:
            with self.subTest(template=bad_template), self.assertRaises(ValueError):
                check_foundation_bindings(data, suite, bad_template)
        for key in ["model_modules", "model_files"]:
            bad_suite = copy.deepcopy(suite)
            bad_suite[key] = []
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "built and hashed"):
                check_foundation_bindings(data, bad_suite, template)


if __name__ == "__main__":
    unittest.main()
