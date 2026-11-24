import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from zipfile import ZipFile

from publish_f_symbols import checked_files


class ArtifactTest(unittest.TestCase):
    def test_publish_only_the_requested_verified_bytes(self):
        payload = b'{}'
        proof = b"test proof bytes"
        digest = hashlib.sha256(payload).hexdigest()
        manifest = {"schema_version": 1, "claim": "pentagon verified", "input_sha256": digest,
                    "verifier_commit": "abc", "proposed_target": {"catalog": "Anyon Atlas", "record_id": "B01-00000"},
                    "verifications": [{"claim_type": "pentagon", "proof": "Proof.lean",
                                       "proof_sha256": hashlib.sha256(proof).hexdigest()}]}
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "bundle.zip"
            with ZipFile(path, "w") as archive:
                archive.writestr("input.json", payload)
                archive.writestr("manifest.json", json.dumps(manifest))
                archive.writestr("Proof.lean", proof)
            archive_digest = hashlib.sha256(path.read_bytes()).hexdigest()
            files = checked_files(path, archive_digest, digest, "B01-00000", "abc")
            self.assertEqual(files["Proof.lean"], proof)
            for checksum, target, commit in [(digest, "B01-00000", "abc"),
                                             (archive_digest, "B03-00019", "abc"),
                                             (archive_digest, "B01-00000", "def")]:
                with self.subTest(target=target, commit=commit), self.assertRaises(ValueError):
                    checked_files(path, checksum, digest, target, commit)
            with ZipFile(path, "a") as archive:
                archive.writestr("extra-file", b"ignore me")
            with self.assertRaisesRegex(ValueError, "unexpected"):
                checked_files(path, hashlib.sha256(path.read_bytes()).hexdigest(),
                              digest, "B01-00000", "abc")
