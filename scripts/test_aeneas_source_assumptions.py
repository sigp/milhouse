"""Keep the approved source-fidelity exception narrow and visible."""

import copy
import json
from pathlib import Path
import runpy
import unittest


ROOT = Path(__file__).resolve().parent.parent
CHECK = runpy.run_path(str(ROOT / "scripts/aeneas-audit-progressive-models.py"))["source_assumptions"]


class SourceAssumptionTests(unittest.TestCase):
    def setUp(self):
        self.policy = json.loads((ROOT / "aeneas-lean/SOURCE_MODEL_ASSUMPTIONS.json").read_text())
        self.node = {"kind": "definition", "module": "Tree.FunsExternal", "name": "core.num.Usize.pow"}
        self.inventory = {"localModelDeclarations": [self.node], "roots": [
            {"label": "new", "nodes": [self.node]}, {"label": "get", "nodes": []}]}

    def test_reports_assumption_and_only_dependent_roots(self):
        report = CHECK(self.policy, self.inventory)
        self.assertEqual(report[0]["status"], "assumed")
        self.assertEqual(report[0]["conservativeDependentRoots"], ["new"])
        self.assertEqual(report[0]["deferredCheck"],
                         "core_pow_agrees in reproducers/pow_models/CheckModels.lean")

    def test_rejects_extra_or_different_exceptions(self):
        for mutate in [
            lambda p: p["assumptions"].append(copy.deepcopy(p["assumptions"][0])),
            lambda p: p["assumptions"][0].update(leanDeclaration="another.function"),
            lambda p: p["assumptions"][0].update(status="proved"),
            lambda p: p["assumptions"][0].update(contract=""),
        ]:
            policy = copy.deepcopy(self.policy)
            mutate(policy)
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                CHECK(policy, self.inventory)

    def test_rejects_axiomatic_or_missing_model(self):
        for kind in ["axiom", "opaque"]:
            inventory = copy.deepcopy(self.inventory)
            inventory["localModelDeclarations"][0]["kind"] = kind
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                CHECK(self.policy, inventory)
        with self.assertRaises(ValueError):
            CHECK(self.policy, {"localModelDeclarations": [], "roots": []})


if __name__ == "__main__":
    unittest.main()
