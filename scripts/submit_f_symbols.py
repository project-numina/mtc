#!/usr/bin/env python3
"""Submit an F-symbol JSON file for pentagon verification."""

import argparse
import base64
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


# Base64 expands 48,000 bytes to 64,000 ASCII characters, leaving room for
# the SHA-256 and JSON envelope within GitHub's 65,535-character input limit.
MAX_INPUT_BYTES = 48_000
ATLAS_ID = re.compile(r"[BF][0-9]{2}-[0-9]{5}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path, help="path to the F-symbol JSON")
    parser.add_argument("--atlas-target", metavar="RECORD_ID",
                        help="optional proposed Anyon Atlas target, for example B03-00019")
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local", type=Path, metavar="OUTPUT_DIR",
                        help="verify locally and save the accepted bundle here")
    target.add_argument("--repo", metavar="OWNER/REPO",
                        help="dispatch verify-f-symbols.yml on the repository's main branch")
    args = parser.parse_args()
    if args.atlas_target is not None and not ATLAS_ID.fullmatch(args.atlas_target):
        parser.error("expected an Anyon Atlas record ID such as B03-00019")
    if args.repo is not None and (
        not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", args.repo)
        or args.repo.split("/")[-1] in (".", "..")
    ):
        parser.error("--repo must be a GitHub repository in OWNER/REPO form")

    try:
        with args.candidate.open("rb") as stream:
            payload = stream.read(MAX_INPUT_BYTES + 1)
        if len(payload) > MAX_INPUT_BYTES:
            parser.error(f"submission exceeds the {MAX_INPUT_BYTES:,}-byte limit")
        inputs = {
            "input_b64": base64.b64encode(payload).decode("ascii"),
            "input_sha256": hashlib.sha256(payload).hexdigest(),
        }
        if args.atlas_target:
            inputs["atlas_target"] = args.atlas_target
        if args.local is not None:
            receiver = Path(__file__).resolve().with_name("verify_f_symbol_submission.py")
            command = [sys.executable, receiver, args.local]
            request = inputs
        else:
            endpoint = f"repos/{args.repo}/actions/workflows/verify-f-symbols.yml/dispatches"
            command = ["gh", "api", "--method", "POST",
                       "--header", "X-GitHub-Api-Version: 2026-03-10",
                       "--input", "-", "--jq", ".html_url", endpoint]
            request = {"ref": "main", "inputs": inputs}
        return subprocess.run(command, input=json.dumps(request), text=True).returncode
    except OSError as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    sys.exit(main())
