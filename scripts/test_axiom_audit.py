"""Regression checks for recursive coverage and the foundational-axiom allowlist."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("check_axioms.py").resolve()


class AxiomAuditTests(unittest.TestCase):
    def run_audit(self, *, extra_source="", extra_axiom="", omit_output=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = root / "FrontierTheorems/Nested/Example.lean"
            module.parent.mkdir(parents=True)
            module.write_text("namespace Example\n@[simp] theorem checked : True := True.intro\n"
                              "def value : Nat := 0\n" + extra_source + "\nend Example\n")
            (root / "Audit.lean").write_text("#print axioms Example.checked\n#print axioms Example.value\n")
            (root / "output.txt").write_text(
                f"'Example.checked' depends on axioms: [propext{extra_axiom}]\n" +
                ("" if omit_output else "'Example.value' does not depend on any axioms\n"))
            return subprocess.run([sys.executable, str(SCRIPT), "output.txt"], cwd=root,
                                  text=True, capture_output=True)

    def test_accepts_standard_axioms_and_axiom_free_definitions(self):
        self.assertEqual(self.run_audit().returncode, 0)

    def test_rejects_missing_audit_output(self):
        self.assertIn("Incomplete axiom audit", self.run_audit(omit_output=True).stderr)

    def test_rejects_admitted_proof_axiom(self):
        self.assertIn("Unexpected axioms", self.run_audit(extra_axiom=", sorryAx").stderr)

    def test_rejects_native_computation_axiom(self):
        self.assertIn("Unexpected axioms", self.run_audit(extra_axiom=", Lean.ofReduceBool").stderr)

    def test_finds_unaudited_theorem_in_nested_file(self):
        result = self.run_audit(extra_source="@[simp] theorem missed : True := True.intro\n")
        self.assertIn("Unaudited declarations", result.stderr)
        self.assertIn("Example.missed", result.stderr)

    def test_finds_unaudited_definition_in_nested_file(self):
        self.assertIn("Unaudited declarations", self.run_audit(extra_source="def missed := 1\n").stderr)


if __name__ == "__main__":
    unittest.main()
