import json
from pathlib import Path
import tempfile
import unittest

from cyclotomic_braid import noncyclotomic_ratio, read_generators, search


class CyclotomicBraidTest(unittest.TestCase):
    def read(self, data):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "matrix.json"
            path.write_text(json.dumps(data))
            return read_generators(path)

    def test_cyclotomic_finite(self):
        order, matrices = self.read({"order": 5, "generators": [[[[0, 1], [0]], [[0], [1]]]]})
        self.assertIsNone(noncyclotomic_ratio(matrices[0], order))
        self.assertEqual(search(order, matrices, 4, 50)["result"], "inconclusive")

    def test_cyclotomic_infinite(self):
        order, matrices = self.read({"order": 5, "generators": [[[[0, 1], [0]], [[0], [2]]]]})
        self.assertEqual(search(order, matrices, 1, 50)["result"], "infinite_projective_image")

    def test_infinite_word_with_finite_order_generators(self):
        # Reduced Burau B_3 at a primitive fifth root of unity.
        data = {"order": 5, "generators": [
            [[[0, -1], [1]], [[0], [1]]],
            [[[1], [0]], [[0, 1], [0, -1]]]]}
        order, matrices = self.read(data)
        self.assertTrue(all(noncyclotomic_ratio(m, order) is None for m in matrices))
        result = search(order, matrices, 2, 100)
        self.assertEqual(result["result"], "infinite_projective_image")
        self.assertEqual(len(result["word"]), 2)

    def test_invertible_but_not_braid_representation(self):
        with self.assertRaisesRegex(ValueError, "braid relation"):
            self.read({"order": 5, "generators": [[[[0, 1]]], [[[1]]]]})


if __name__ == "__main__":
    unittest.main()
