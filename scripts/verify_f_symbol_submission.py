#!/usr/bin/env python3
"""Verify a submitted F-table from a JSON envelope on stdin and save its evidence."""

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from submit_f_symbols import ATLAS_ID, MAX_INPUT_BYTES
from atlas_fusion_matches import check_atlas_matches
from verify_pentagon import MODULE, ROOT, fields, unique_object, verify


MAX_ENVELOPE_BYTES = 65_535


def read_submission(stream):
    envelope = stream.read(MAX_ENVELOPE_BYTES + 1)
    if len(envelope) > MAX_ENVELOPE_BYTES:
        raise ValueError(f"submission envelope exceeds {MAX_ENVELOPE_BYTES} bytes")
    submission = json.loads(envelope, object_pairs_hook=unique_object)
    target = submission.pop("atlas_target", "") if isinstance(submission, dict) else ""
    if not isinstance(target, str) or (target and not ATLAS_ID.fullmatch(target)):
        raise ValueError("invalid proposed Anyon Atlas record ID")
    fields(submission, "input_b64 input_sha256", "submission")
    encoded = submission["input_b64"]
    digest = submission["input_sha256"]
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("input_sha256 must be a lowercase SHA-256 hex digest")
    if not isinstance(encoded, str):
        raise ValueError("input_b64 must be a base64 string")
    payload = base64.b64decode(encoded, validate=True)
    if len(payload) > MAX_INPUT_BYTES:
        raise ValueError(f"input exceeds {MAX_INPUT_BYTES} bytes")
    if hashlib.sha256(payload).hexdigest() != digest:
        raise ValueError("submitted bytes do not match input_sha256")
    return payload, digest, target or None


def verifier_commit():
    commit = subprocess.check_output(["git", "rev-parse", "--verify", "HEAD"], cwd=ROOT,
                                     text=True).strip()
    imports = json.loads(subprocess.check_output(
        ["lake", "query", "--json", f"+{MODULE}:transImports"], cwd=ROOT))
    sources = ["scripts/verify_pentagon.py", "lean-toolchain", "lakefile.toml", "lake-manifest.json"]
    sources.extend(name.replace(".", "/") + ".lean" for name in [MODULE, *imports]
                   if name.startswith("MTC."))
    changed = subprocess.check_output(
        ["git", "diff", "--name-only", commit, "--", *sources], cwd=ROOT, text=True)
    if changed:
        paths = ", ".join(changed.splitlines())
        raise ValueError(f"verifier sources differ from commit {commit}: {paths}")
    return commit


def save_verified_submission(payload, digest, output, target=None):
    if os.path.lexists(output):
        raise FileExistsError(f"output path already exists: {output}")
    commit = verifier_commit()
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=output.parent) as scratch:
        bundle = Path(scratch) / "bundle"
        bundle.mkdir()
        source = bundle / "input.json"
        source.write_bytes(payload)
        if verify(source, bundle / "Proof.lean") != digest:
            raise ValueError("verifier read a different input digest")
        manifest = {"schema_version": 1, "claim": "pentagon verified", "input_sha256": digest,
                    "verifier_commit": commit, "verifications": []}
        if target:
            manifest["proposed_target"] = {"catalog": "Anyon Atlas", "record_id": target}
        proofs = [("pentagon", "Proof.lean")]
        atlas = check_atlas_matches(payload, bundle)
        if atlas is not None:
            manifest["atlas_fusion"] = atlas
            if atlas["matches"]:
                proofs.append(("atlas_fusion_rules_match", atlas["proof"]))
        for kind, filename in proofs:
            manifest["verifications"].append({
                "claim_type": kind, "proof": filename,
                "proof_sha256": hashlib.sha256((bundle / filename).read_bytes()).hexdigest(),
            })
        metadata = json.dumps(manifest, indent=2) + "\n"
        (bundle / "manifest.json").write_text(metadata, encoding="utf-8")
        if os.path.lexists(output):
            raise FileExistsError(f"output path already exists: {output}")
        bundle.rename(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new directory for the verified submission")
    args = parser.parse_args()
    try:
        payload, digest, target = read_submission(sys.stdin.buffer)
        save_verified_submission(payload, digest, args.output, target)
    except (OSError, ValueError, RecursionError, OverflowError, subprocess.CalledProcessError) as error:
        print(f"Submission failed: {error}", file=sys.stderr)
        return 1
    print(f"Verified all pentagons for input SHA-256 {digest}. Evidence saved in {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
