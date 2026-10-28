import json
from pathlib import Path
import tempfile
import unittest

import sympy as sp

from braid_infinite import noncyclotomic_ratio, read_generators, search


class BraidImageTest(unittest.TestCase):
    def test_projective_infinite_burau(self):
        # Reduced B_3 Burau matrices at t=2: this is a test fixture, not an anyon.
        a = sp.ImmutableMatrix([[-2, 1], [0, 1]])
        b = sp.ImmutableMatrix([[1, 0], [2, -2]])
        self.assertEqual(a * b * a, b * a * b)
        result = search([a, b], 2, 100)
        self.assertEqual(result["result"], "infinite_projective_image")
        self.assertTrue(result["noncyclotomic_factor"])

    def test_finite_symmetric_group_image(self):
        a = sp.ImmutableMatrix([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
        b = sp.ImmutableMatrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]])
        self.assertIsNone(noncyclotomic_ratio(a))
        self.assertEqual(search([a, b], 5, 100)["result"], "inconclusive")

    def test_reject_invalid_braid_relations(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.json"
            path.write_text(json.dumps({"generators": [[[2, 0], [0, 1]], [[1, 0], [0, 1]]]}))
            with self.assertRaisesRegex(ValueError, "braid relation"):
                read_generators(path)


if __name__ == "__main__":
    unittest.main()
