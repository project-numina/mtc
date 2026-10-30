"""Regression tests for the lexical boundary around unproved conjectures."""
import unittest
from pathlib import Path

from audit_new_libraries import check_sorry_scope, code_without_comments_and_strings


class SorryScopeTests(unittest.TestCase):
    def setUp(self):
        self.fields = {"Declaration": "MTC.Conjectures.Test.goal", "Status": "open"}
        self.path = Path("MTC/Conjectures/Test/Goal.lean")

    def check(self, text):
        check_sorry_scope(self.path, code_without_comments_and_strings(text), self.fields)

    def test_named_conjecture(self):
        self.check('theorem goal : True := by\n  sorry\n')

    def test_sorry_in_example_is_rejected(self):
        with self.assertRaises(ValueError):
            self.check('theorem goal : True := by\n  sorry\nexample : False := by\n  sorry\n')

    def test_admit_in_example_is_rejected(self):
        with self.assertRaises(ValueError):
            self.check('theorem goal : True := by sorry\nexample : False := by admit\n')

    def test_sorry_in_type_is_rejected(self):
        with self.assertRaises(ValueError):
            self.check('theorem goal : (by sorry) := by trivial\n')

    def test_formalized_cannot_use_sorry(self):
        self.fields["Status"] = "proved"
        with self.assertRaises(ValueError):
            self.check('theorem goal : True := by sorry\n')

    def test_nested_comments_and_strings_are_ignored(self):
        self.check('/- sorry /- sorry -/ -/\ndef text := "sorry"\n-- sorry\n')


if __name__ == "__main__":
    unittest.main()
