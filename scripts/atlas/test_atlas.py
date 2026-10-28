#!/usr/bin/env python3
"""Regression checks for parsing, joins, and the modular diagnostic."""
import importlib.util
import unittest
from pathlib import Path


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


atlas = module('atlas_import_test', 'import.py')
validate = module('atlas_validate_test', 'validate.py')


class AtlasTests(unittest.TestCase):
    def test_cyclotomic_parser(self):
        self.assertEqual(atlas.parse_expression('-2 + E(1/4) - 3*E(2/5)'),
                         [(-2, 1, 0, 1), (1, 1, 1, 4), (-3, 1, 2, 5)])
        self.assertEqual(atlas.parse_expression('1/2*E(2/4)'), [(1, 2, 1, 2)])
        for bad in ('', 'E(1/0)', 'E(1/4);print(3)', 'E(1/4)E(1/4)', 'E(-1/4)'):
            with self.subTest(bad=bad), self.assertRaises((ValueError, ZeroDivisionError)):
                atlas.parse_expression(bad)

    def test_semion_diagnostic_catches_corruption(self):
        ids = {'rank': 2, 'kind': 'bosonic', 'quantumDimensions': ['1', '1'], 'twists': ['1', 'E(1/4)']}
        modular = {'S': [['1', '1'], ['1', '-1']], 'T': ids['twists'], 'tEncoding': 'diagonal'}
        structure = {'propertiesRealizations': {'frobeniusSchurExponent': 4}}
        fusion = {'rank': 2, 'encoding': 'compact-sparse-commutative-v1', 'lifts': [{'offsets': [0, 2, 4, 6], 'terms': [0, 1, 1, 1, 0, 1]}]}
        self.assertEqual(validate.check('bosonic', 2, ids, modular, structure, fusion, 1e-8), [])
        modular['S'][1][1] = '1'
        self.assertIn('S squared / charge conjugation', validate.check('bosonic', 2, ids, modular, structure, fusion, 1e-8))


if __name__ == '__main__':
    unittest.main()
