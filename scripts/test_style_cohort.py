import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / 'style'))
from survey import match_cohort


class StyleCohortTest(unittest.TestCase):
    def test_move_preserves_identity_and_missing_and_new_are_reported(self):
        baseline = [{'qualified_name': 'A.old'}, {'qualified_name': 'A.kept'}]
        current = [{'env': {'name': 'A.kept'}, 'file': 'new-path'},
                   {'env': {'name': 'A.new'}}, {'name': 'unmatched'}]
        pairs, missing, extra = match_cohort(baseline, current)
        self.assertEqual([(a['qualified_name'], b['file']) for a, b in pairs],
                         [('A.kept', 'new-path')])
        self.assertEqual([d['qualified_name'] for d in missing], ['A.old'])
        self.assertEqual(len(extra), 2)

    def test_ambiguous_identity_is_not_silently_paired(self):
        baseline = [{'qualified_name': 'A.x'}]
        current = [{'env': {'name': 'A.x'}}, {'env': {'name': 'A.x'}}]
        pairs, missing, extra = match_cohort(baseline, current)
        self.assertEqual((len(pairs), len(missing), len(extra)), (0, 1, 2))

    def test_bad_baseline_fails(self):
        with self.assertRaises(ValueError):
            match_cohort([{'qualified_name': 'A.x'}, {'qualified_name': 'A.x'}], [])


if __name__ == '__main__':
    unittest.main()
