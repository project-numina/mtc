#!/usr/bin/env python3
"""Small format checks for the local Atlas block reader."""
import io
import unittest

from import_atlas_block import read_block


class BlockReaderTest(unittest.TestCase):
    def test_sparse_coefficients_and_r_padding(self):
        # R(1,2;3), one row and two columns. The first element is
        # (1 - 2*zeta)/2; the second is zero.
        payload = bytes([
            1, 2, 3, 255, 1, 0, 2, 0,
            2, 3, 0, 0, 0, 0,  # mask 0b11, then zero mask
            2,  # common denominator
            2, 3,  # zigzag-encoded coefficients +1 and -2
        ])
        labels, rows, cols, entries = read_block(io.BytesIO(payload), 2, 2)
        self.assertEqual((labels, rows, cols), ((1, 2, 3), 1, 2))
        self.assertEqual(entries, [(2, [1, -2]), (1, [0, 0])])

    def test_truncated_block_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "truncated"):
            read_block(io.BytesIO(bytes([1, 2, 3])), 2, 1)

    def test_nonzero_padding_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "padding"):
            read_block(io.BytesIO(bytes([1, 2, 3, 0])), 2, 2)


if __name__ == "__main__":
    unittest.main()
