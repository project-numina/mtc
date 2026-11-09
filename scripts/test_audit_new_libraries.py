"""Regression tests for strict placeholder rejection and comment masking."""
import unittest
from audit_new_libraries import SORRY, code_without_comments_and_strings

class ProofSourceTests(unittest.TestCase):
    def test_placeholders_in_every_proof_form_are_detected(self):
        for text in ("theorem goal : True := by sorry",
                     "example : False := by admit",
                     "def bad : Nat := by sorry",
                     "theorem goal : (by sorry) := by trivial"):
            with self.subTest(text=text):
                self.assertIsNotNone(SORRY.search(code_without_comments_and_strings(text)))

    def test_nested_comments_and_strings_are_ignored(self):
        text = '/- sorry /- admit -/ -/\ndef text := "sorry"\n-- admit\n'
        self.assertIsNone(SORRY.search(code_without_comments_and_strings(text)))

    def test_mask_preserves_offsets_and_newlines(self):
        text = '/- outer\n /- inner -/ -/\ntheorem goal : True := by sorry\n'
        masked = code_without_comments_and_strings(text)
        self.assertEqual(len(masked), len(text))
        self.assertEqual(masked.count("\n"), text.count("\n"))
        self.assertEqual(SORRY.search(masked).start(), text.rindex("sorry"))

    def test_identifier_substrings_are_not_placeholders(self):
        self.assertIsNone(SORRY.search("sorry_count admitted sorry'"))

if __name__ == "__main__":
    unittest.main()
