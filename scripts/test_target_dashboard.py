import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'style'))
from source_metrics import ROOT, parse
import source_metrics
import target_dashboard
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

    def test_proof_valued_definition_is_in_census(self):
        with tempfile.TemporaryDirectory(dir=ROOT / 'scratch') as dirname:
            root = Path(dirname)
            (root / 'MTC').mkdir()
            (root / 'style').mkdir()
            (root / 'out').mkdir()
            (root / 'MTC' / 'Example.lean').write_text(
                '@[inline] private def proof_helper : True := by\n  trivial\n'
                'def data_helper : Nat := 0\n')
            (root / 'style' / '.environment.tsv').write_text(
                'module\tname\tkind\texplicit\timplicit\tstrict\tinstance\thypotheses\ttype_hash\n'
                'MTC.Example\t_private.MTC.Example.0.proof_helper\tdefinition\t0\t0\t0\t0\t0\t1\n'
                'MTC.Example\tdata_helper\tdefinition\t0\t0\t0\t0\t0\t2\n')
            (root / 'style' / '.proposition-definitions.tsv').write_text(
                'module\tname\nMTC.Example\t_private.MTC.Example.0.proof_helper\n')
            (root / 'out' / 'cohort-files-fb6ec518.tsv').write_text('file\tpopulation\n')
            (root / 'out' / 'cohort-fb6ec518-expanded.tsv').write_text(
                'population\tqualified_name\tfile\tline\tkind\tname\n')
            with patch.object(target_dashboard, 'ROOT', root), \
                 patch.object(target_dashboard, 'STYLE', root / 'style'), \
                 patch.object(target_dashboard, 'OUT', root / 'out'), \
                 patch.object(source_metrics, 'ROOT', root):
                result = target_dashboard.snapshot()
            self.assertEqual([r['name'] for r in result], ['proof_helper'])
            self.assertEqual(result[0]['match'], 'unique')
            self.assertEqual(result[0]['proof_lines'], 2)


if __name__ == '__main__':
    unittest.main()
