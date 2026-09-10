"""Reject malformed intrinsic boundaries and changes to the supported caller."""

import copy
import unittest

from aeneas_source_model_audit import POW_SELECTOR_CALLER, prepare_pow_selector


class PowSelectorTests(unittest.TestCase):
    def setUp(self):
        self.source = {
            "def_id": 2, "is_global_initializer": None,
            "body": {"Intrinsic": {"name": "is_val_statically_known", "arg_names": ["_arg"]}},
            "item_meta": {
                "name": [{"Ident": [part, 0]} for part in
                         ["core", "intrinsics", "is_val_statically_known"]],
                "span": {"data": {"file_id": 4}}, "is_local": False, "opacity": "Foreign",
            },
        }
        self.data = {"translated": {"crate_name": "pow_source", "fun_decls": [self.source],
            "files": [{"id": 4, "crate_name": "core",
                       "name": {"Local": "/rustc/library/core/src/intrinsics/mod.rs"}}]}}
        self.template = (
            "axiom core.intrinsics.is_val_statically_known\n"
            "  {T : Type} (markerCopyInst : core.marker.Copy T) : T → Result Bool\n")
        self.original = ("import Aeneas\nnamespace PowSource\n"
            "\ndef core.num.Usize.pow_loop0 := originalLoop0\n"
            "\ndef core.num.Usize.pow_loop1 := originalLoop1\n"
            + POW_SELECTOR_CALLER + "\n/-- [pow_source::pow]: -/\n"
            "def pow := core.num.Usize.pow\nend PowSource\n")

    def test_only_section_parameter_changes(self):
        data = copy.deepcopy(self.data)
        prepared, record = prepare_pow_selector(self.data, self.template, self.original)
        parameter = "\nvariable [PowSource.StaticKnown]\n"
        self.assertEqual(prepared.count(parameter), 1)
        self.assertEqual(prepared.replace(parameter, "", 1), self.original)
        self.assertEqual(self.data, data)
        self.assertEqual(record["outcomes"], [False, True])
        self.assertNotEqual(record["originalFunsSha256"], record["parameterizedFunsSha256"])

    def test_rejects_extra_or_malformed_template_declarations(self):
        for template in [self.template + "\naxiom another : Bool\n",
                         self.template.replace("Result Bool", "Bool"),
                         self.template.replace("axiom", "opaque"),
                         self.template + "\ndef replacement := true\n",
                         self.template + "\nsorry\n"]:
            with self.subTest(template=template), self.assertRaises(ValueError):
                prepare_pow_selector(self.data, template, self.original)

    def test_rejects_invalid_intrinsic_provenance(self):
        for mutate in [
            lambda d: d["translated"].update(crate_name="another"),
            lambda d: d["translated"]["fun_decls"][0].update(body="Opaque"),
            lambda d: d["translated"]["fun_decls"][0].update(is_global_initializer=0),
            lambda d: d["translated"]["fun_decls"][0]["item_meta"].update(is_local=True),
            lambda d: d["translated"]["fun_decls"][0]["item_meta"].update(opacity="Transparent"),
            lambda d: d["translated"]["files"][0].update(crate_name="pow_source"),
            lambda d: d["translated"]["files"][0].update(name={"Local": "substitute.rs"}),
        ]:
            data = copy.deepcopy(self.data)
            mutate(data)
            with self.subTest(data=data), self.assertRaises(ValueError):
                prepare_pow_selector(data, self.template, self.original)

    def test_rejects_changed_call_control_flow_or_scope(self):
        call = "    let b ← core.intrinsics.is_val_statically_known core.marker.CopyU32 exp\n"
        for original in [self.original.replace(call, ""),
                         self.original.replace(call, call + call),
                         self.original.replace(call, "    let b ← core.num.Usize.pow self exp\n"),
                         self.original.replace("  if exp = 0#u32", "  if exp = 1#u32"),
                         self.original.replace("namespace PowSource", "namespace Other"),
                         self.original + "\nvariable [PowSource.StaticKnown]\n",
                         self.original.replace(call, "") + call]:
            with self.subTest(original=original), self.assertRaises(ValueError):
                prepare_pow_selector(self.data, self.template, original)


if __name__ == "__main__":
    unittest.main()
