import itertools
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from verify_pentagon import ROOT, cyclotomic, proof_source, read_table


ISING = ROOT / "MTC/FRSymbols/Ising.json"
VERIFY = ROOT / "scripts/verify_pentagon.py"


class TableInputTest(unittest.TestCase):
    def setUp(self):
        self.data = json.loads(ISING.read_bytes())

    def rejected(self, message):
        with self.assertRaisesRegex(ValueError, message):
            read_table(json.dumps(self.data).encode())

    def test_missing_and_duplicate_blocks(self):
        block = self.data["blocks"].pop()
        self.rejected("missing F block")
        self.data["blocks"].extend([block, block])
        self.rejected("duplicate F block")

    def test_duality_and_unit_conventions(self):
        self.data["dual"] = [0, 2, 1]
        self.rejected("fusion duality law")
        self.data["dual"] = [0, 1, 2]
        self.data["strict_unit"] = False
        self.rejected("missing F block")
        self.data["strict_unit"] = True
        self.data["blocks"].append({"labels": [0, 0, 0, 0], "rows": [[[-1]]]})
        self.rejected("strict-unit block")

    def test_coordinate_validation(self):
        row = self.data["blocks"][0]["rows"][0]
        for bad in (True, 0.5, "1/0", "0]\nsorry"):
            with self.subTest(bad=bad):
                row[0] = [bad]
                self.rejected("rational coordinate")
        row[0] = [0] * 5
        self.rejected("power-basis degree")

    def test_duplicate_json_key(self):
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            read_table(b'{"order":1,"order":8}')

    def test_multiplicity_basis_dimensions(self):
        # x*x = 1 + 2x. The two non-unit blocks have sizes 2 and 5.
        data = {
            "version": 1, "order": 1, "unit": 0, "dual": [0, 1],
            "fusion": [[[1, 0], [0, 1]], [[0, 1], [1, 2]]],
            "strict_unit": True,
            "blocks": [{"labels": [1, 1, 1, d], "rows": [[[1]] * size for _ in range(size)]}
                       for d, size in enumerate((2, 5))],
        }
        *_, blocks = read_table(json.dumps(data).encode())
        by_key = dict(zip(itertools.product(range(2), repeat=4), blocks))
        self.assertEqual(by_key[0, 1, 1, 1], [(1,), (), (), (1,)])
        self.assertEqual(len(by_key[1, 1, 1, 1]), 25)
        data["blocks"][1]["rows"].pop()
        with self.assertRaisesRegex(ValueError, "length 5"):
            read_table(json.dumps(data).encode())

    def test_cyclotomic_polynomial_remainder_convention(self):
        self.assertEqual(cyclotomic(1), (-1, 1))
        self.assertEqual(cyclotomic(8), (1, 0, 0, 0, 1))
        self.assertEqual(cyclotomic(15), (1, -1, 0, 1, -1, 1, 0, -1, 1))
        self.assertIn("monicTail := [1, 0, 0, 0]", proof_source(ISING.read_bytes()))


@unittest.skipUnless(shutil.which("lake"), "Lean toolchain required for kernel replay")
class KernelTest(unittest.TestCase):
    def check_table(self, input_path, proof):
        return subprocess.run([sys.executable, VERIFY, input_path, "--proof", proof],
                              cwd=ROOT, capture_output=True, text=True)

    def test_ising_proof_and_mutation(self):
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory) / "IsingPentagon.lean"
            positive = self.check_table(ISING, proof)
            self.assertEqual(positive.returncode, 0, positive.stdout + positive.stderr)
            checked = proof.read_bytes()
            self.assertEqual(checked.decode(), proof_source(ISING.read_bytes()))
            # The four-psi pentagon requires F_psi^(psi psi psi) squared to be 1.
            invalid = json.loads(ISING.read_bytes())
            invalid["blocks"][-1]["rows"] = [[[2]]]
            invalid_path = Path(directory) / "mutated.json"
            invalid_path.write_text(json.dumps(invalid))
            negative = self.check_table(invalid_path, proof)
            self.assertNotEqual(negative.returncode, 0)
            self.assertIn("Verification failed", negative.stderr)
            self.assertIn("Failing pentagon (a,b,c,d,u,e,f,g,h,α,β,γ,δ,ζ,η)", negative.stdout)
            self.assertEqual(proof.read_bytes(), checked)

    def test_failure_in_nonzero_multiplicity_channel(self):
        # Only the last row/column of F_1^(111) is nonzero: the resulting
        # pentagon 2*2 = 2*2*2 has every external vertex index equal to 1.
        fusion = [[[1, 0], [0, 1]], [[0, 1], [1, 2]]]
        blocks = []
        for a, b, c, d in itertools.product(range(2), repeat=4):
            width = sum(fusion[a][b][e] * fusion[e][c][d] for e in range(2))
            if width:
                rows = [[[] for _ in range(width)] for _ in range(width)]
                if (a, b, c, d) == (1, 1, 1, 1):
                    rows[-1][-1] = [2]
                blocks.append({"labels": [a, b, c, d], "rows": rows})
        data = dict(version=1, order=1, unit=0, dual=[0, 1],
                    fusion=fusion, strict_unit=False, blocks=blocks)
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "multiplicity.json"
            proof = Path(directory) / "Multiplicity.lean"
            source.write_text(json.dumps(data))
            result = self.check_table(source, proof)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("#[" + ", ".join(["1"] * 15) + "]", result.stdout)
            self.assertFalse(proof.exists())


if __name__ == "__main__":
    unittest.main()
