import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / 'style'))
from source_metrics import ROOT, parse


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


if __name__ == '__main__':
    unittest.main()
