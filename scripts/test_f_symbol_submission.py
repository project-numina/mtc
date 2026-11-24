import base64
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import submit_f_symbols as client
import verify_f_symbol_submission as receiver
from atlas_fusion_matches import PACK, PACK_SHA256, dense_fusion, label_maps


class SubmissionTest(unittest.TestCase):
    def test_ising_atlas_label_maps(self):
        source = json.loads((receiver.ROOT / "MTC/FRSymbols/Ising.json").read_bytes())
        packed = PACK.read_bytes()
        self.assertEqual(hashlib.sha256(packed).hexdigest(), PACK_SHA256)
        rows = json.loads(gzip.decompress(packed))["records"]
        self.assertEqual(len(rows), 24)
        matches = {r["id"]: list(label_maps(source, dense_fusion(r))) for r in rows}
        self.assertEqual([k for k, maps in matches.items() if maps],
                         [f"B03-{n:05d}" for n in range(8, 24)])
        self.assertEqual(matches["B03-00019"], [[0, 2, 1]])
        self.assertEqual(matches["B03-00011"], [[0, 1, 2]])

    def test_local_and_remote_send_identical_bytes(self):
        data = '{"label": "σ"}\r\n'.encode("utf-8")
        expected = (data, hashlib.sha256(data).hexdigest(), "B03-00019")
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / "candidate table.json"
            candidate.write_bytes(data)
            output = Path(directory) / "result"
            for mode, target in (("--local", str(output)), ("--repo", "owner/name")):
                with self.subTest(mode=mode), patch.object(
                    sys, "argv", ["submit", str(candidate), mode, target, "--atlas-target", "B03-00019"]
                ), patch.object(client.subprocess, "run") as invoke:
                    invoke.return_value.returncode = 0
                    self.assertEqual(client.main(), 0)
                    command, = invoke.call_args.args
                    request = json.loads(invoke.call_args.kwargs["input"])
                    if mode == "--repo":
                        self.assertEqual(command[:2], ["gh", "api"])
                        self.assertIn("repos/owner/name/actions/workflows/publish-atlas.yml/dispatches", command)
                        self.assertEqual(command[command.index("--jq") + 1], ".html_url")
                        self.assertEqual(request["ref"], "main")
                        request = request["inputs"]
                    else:
                        self.assertEqual(Path(command[1]).name, "verify_f_symbol_submission.py")
                        self.assertEqual(Path(command[2]), output)
                    stream = io.BytesIO(json.dumps(request).encode())
                    self.assertEqual(receiver.read_submission(stream), expected)

    def test_receiver_enforces_size_and_digest(self):
        for size, corrupt, error in (
            (client.MAX_INPUT_BYTES, False, None),
            (client.MAX_INPUT_BYTES + 1, False, "exceeds"),
            (1, True, "do not match"),
        ):
            with self.subTest(size=size, corrupt=corrupt):
                data = b"x" * size
                digest = "0" * 64 if corrupt else hashlib.sha256(data).hexdigest()
                request = {"input_b64": base64.b64encode(data).decode(), "input_sha256": digest}
                stream = io.BytesIO(json.dumps(request).encode())
                if error:
                    with self.assertRaisesRegex(ValueError, error):
                        receiver.read_submission(stream)
                else:
                    self.assertEqual(receiver.read_submission(stream), (data, digest, None))

    def test_failed_verification_leaves_no_bundle(self):
        data = b"{}"
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "bundle"
            with patch.object(receiver, "verifier_commit", return_value="a" * 40), \
                 patch.object(receiver, "verify", side_effect=subprocess.CalledProcessError(1, "lean")), \
                 self.assertRaises(subprocess.CalledProcessError):
                receiver.save_verified_submission(data, hashlib.sha256(data).hexdigest(), output)
            self.assertEqual(list(Path(directory).iterdir()), [])


if __name__ == "__main__":
    unittest.main()
