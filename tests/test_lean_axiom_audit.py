import importlib.util
from pathlib import Path
import unittest


spec = importlib.util.spec_from_file_location(
    "check_lean_axioms", Path(__file__).resolve().parents[1] / "scripts/check_lean_axioms.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class LeanAxiomAudit(unittest.TestCase):
    SOURCE = "import Math115\n#print axioms A\n#print axioms B\n"
    OUTPUT = "'A' does not depend on any axioms\n'B' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"

    def test_empty_and_multiline_axiom_reports_are_both_counted(self):
        records = audit.check_audit(self.SOURCE, self.OUTPUT)
        self.assertEqual([r["name"] for r in records], ["A", "B"])
        self.assertEqual(records[0]["axioms"], [])
        self.assertEqual(set(records[1]["axioms"]), audit.ALLOWED)

    def test_missing_duplicated_unrequested_or_reordered_reports_fail(self):
        for output in (self.OUTPUT.split("'B'")[0], self.OUTPUT + self.OUTPUT,
                       self.OUTPUT + "'C' does not depend on any axioms\n",
                       "'B' does not depend on any axioms\n'A' does not depend on any axioms\n"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                audit.check_audit(self.SOURCE, output)

    def test_nonstandard_axioms_fail(self):
        for name in ("sorryAx", "customAxiom"):
            with self.subTest(axiom=name), self.assertRaises(ValueError):
                audit.check_audit(self.SOURCE, self.OUTPUT.replace("propext", name))

    def test_empty_or_duplicate_requests_fail(self):
        for source in ("import Math115\n", self.SOURCE + "#print axioms A\n"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                audit.check_audit(source, self.OUTPUT)

    def test_unrecognized_lean_report_fails_closed(self):
        for output in (self.OUTPUT.replace("does not depend on any axioms", "unknown report format"),
                       self.OUTPUT + "noise: failed compilation\n",
                       self.OUTPUT.replace("'B'", "WARNING: inspect this\n'B'")):
            with self.subTest(output=output), self.assertRaises(ValueError):
                audit.check_audit(self.SOURCE, output)


if __name__ == "__main__":
    unittest.main()
