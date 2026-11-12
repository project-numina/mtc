import unittest
from pathlib import Path

from check_pivotal_invariants import declaration, digest, GENERATED, ROOT


class PivotalInvariantsTest(unittest.TestCase):
    def test_generated_definitions_match_baseline_and_detect_changes(self):
        text = (ROOT / 'MTC/PropertyF/Pivotal/GeneratedCategory.lean').read_text(encoding='utf-8')
        for name, expected in GENERATED.items():
            with self.subTest(name=name):
                source = declaration(text, name)
                self.assertEqual(digest(source), expected)
                self.assertNotEqual(digest(source + b' changed'), expected)

    def test_missing_definition_is_rejected(self):
        with self.assertRaises(ValueError):
            declaration('def another := True', 'ObjectwiseStatement')


if __name__ == '__main__':
    unittest.main()
