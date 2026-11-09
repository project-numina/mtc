import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / 'style'))
from source_metrics import ROOT, parse
from target_dashboard import target_gap


class ExpandedSourceMetricsTest(unittest.TestCase):
    def test_inline_attributes_and_anonymous_proof(self):
        source = '''@[simp] theorem inline_result : True := by
  trivial

private lemma named_result : True := by
  trivial

local instance (n : Nat) : Fact (n = n) := by
  exact ⟨rfl⟩
'''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=ROOT / 'scratch') as f:
            f.write(source)
            f.flush()
            old = parse(Path(f.name), 'Test')
            new = parse(Path(f.name), 'Test', include_inline_attributes=True, count_all_proofs=True)
        self.assertNotIn('inline_result', [r['name'] for r in old['declarations']])
        result = {r['name']: r for r in new['declarations'] if r['proof_lines']}
        self.assertEqual(set(result), {'inline_result', 'named_result', '(anonymous)'})
        self.assertEqual(result['inline_result']['proof_lines'], 2)
        self.assertEqual(result['named_result']['proof_lines'], 2)
        self.assertEqual(result['(anonymous)']['proof_lines'], 2)
        self.assertEqual(result['(anonymous)']['steps'], 1)


class TargetGapTest(unittest.TestCase):
    def test_ties_and_interpolation(self):
        median = target_gap([1, 2, 3, 3, 4, 4, 5, 6], .5, 3, 1)
        self.assertEqual(median['boundary_values'], [3, 4])
        self.assertEqual(median['equal_to_target'], 2)
        self.assertEqual(median['minimum_distinct_reductions_relaxed'], 1)
        # The quantile can meet its target even if the upper boundary exceeds
        # it, so simply requiring both boundary values <= target overcounts.
        interpolated = target_gap([0, 0, 1, 3], .5, .5, 0)
        self.assertEqual(interpolated['minimum_distinct_reductions_relaxed'], 0)
        self.assertIsNone(target_gap([], .5, 2, 0))


if __name__ == '__main__':
    unittest.main()
