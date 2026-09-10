"""Check mixed dependency provenance without weakening the original crate gate."""

import copy
import unittest

from aeneas_source_model_audit import check_llbc


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


if __name__ == "__main__":
    unittest.main()
