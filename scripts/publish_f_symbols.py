"""Publish a verified artifact from publish-atlas.yml to the private Numina dataset."""

import hashlib
import json
import os
from pathlib import Path
import sys
from zipfile import ZipFile

from atlas_fusion_matches import PACK, PACK_SHA256
from submit_f_symbols import ATLAS_ID


REPO = "project-numina/anyon-atlas-symbols"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(obj):
    return (json.dumps(obj, indent=2) + "\n").encode()


def checked_files(path, archive_digest, digest, target, commit):
    if sha256(path.read_bytes()) != archive_digest:
        raise ValueError("archive differs from the artifact saved by the verifier")
    if target and not ATLAS_ID.fullmatch(target):
        raise ValueError("invalid proposed Atlas ID")
    with ZipFile(path) as archive:
        manifest = json.loads(archive.read("manifest.json"))
        proposal = {"catalog": "Anyon Atlas", "record_id": target} if target else None
        if (manifest["schema_version"] != 1 or manifest["claim"] != "pentagon verified"
                or manifest["input_sha256"] != digest or manifest["verifier_commit"] != commit
                or manifest.get("proposed_target") != proposal):
            raise ValueError("manifest differs from the verified dispatch")
        names = {"input.json", "manifest.json", "Proof.lean"}
        proofs = {"pentagon": "Proof.lean"}
        if "atlas_fusion" in manifest:
            names.add(PACK.name)
            if sha256(archive.read(PACK.name)) != PACK_SHA256:
                raise ValueError("Atlas snapshot checksum mismatch")
            if manifest["atlas_fusion"]["matches"]:
                names.add("AtlasFusion.lean")
                proofs["atlas_fusion_rules_match"] = "AtlasFusion.lean"
        if sorted(archive.namelist()) != sorted(names):
            raise ValueError("unexpected or missing files in artifact")
        files = {name: archive.read(name) for name in names}
    if sha256(files["input.json"]) != digest:
        raise ValueError("input checksum mismatch")
    for check in manifest["verifications"]:
        filename = proofs.pop(check["claim_type"])
        if filename != check["proof"] or sha256(files[filename]) != check["proof_sha256"]:
            raise ValueError("proof checksum mismatch")
    if proofs:
        raise ValueError("missing verification record")
    return files


def publish(files, digest, target):
    from huggingface_hub import CommitOperationAdd, HfApi, hf_hub_download
    from huggingface_hub.errors import HfHubHTTPError

    api = HfApi(endpoint="https://huggingface.co", token=True)
    root = f"f_submissions/{digest}"
    base_manifest = root + "/manifest.json"
    proposal_file = root + f"/proposals/{target}.json"

    def read(name, revision):
        path = hf_hub_download(REPO, name, repo_type="dataset", revision=revision,
                               endpoint=api.endpoint, token=True)
        return Path(path).read_bytes()

    for attempt in range(5):
        info = api.dataset_info(REPO, revision="main", timeout=30)
        if info.private is not True:
            raise ValueError("publication requires a private dataset")
        entries = api.get_paths_info(REPO, [root, base_manifest, proposal_file],
                                     repo_type="dataset", revision=info.sha)
        present = {entry.path for entry in entries}
        if root not in present:
            additions = {f"{root}/{name}": data for name, data in files.items()}
        else:
            if base_manifest not in present or read(root + "/input.json", info.sha) != files["input.json"]:
                raise ValueError("existing input directory conflicts with submission")
            existing = json.loads(read(base_manifest, info.sha))
            if existing["input_sha256"] != digest or existing["claim"] != "pentagon verified":
                raise ValueError("existing manifest conflicts with submission")
            proposed = {"catalog": "Anyon Atlas", "record_id": target}
            if not target or existing.get("proposed_target") == proposed:
                return info.sha, root, "already present"
            if proposal_file in present:
                previous = json.loads(read(proposal_file, info.sha))
                if previous["input_sha256"] != digest or previous["proposed_target"] != proposed:
                    raise ValueError("existing proposal conflicts with submission")
                return info.sha, root, "already present"
            additions = {proposal_file: json_bytes({"input_sha256": digest, "proposed_target": proposed,
                                                    "github_run": json.loads(files["github-run.json"])})}
        try:
            result = api.create_commit(
                repo_id=REPO, repo_type="dataset", revision="main", parent_commit=info.sha,
                commit_message=f"Record verified F-symbol submission {digest[:12]}",
                operations=[CommitOperationAdd(path_in_repo=name, path_or_fileobj=data)
                            for name, data in sorted(additions.items())])
        except HfHubHTTPError:
            if attempt == 4 or api.dataset_info(REPO, revision="main").sha == info.sha:
                raise
            continue
        if api.dataset_info(REPO, revision=result.oid).private is not True:
            raise ValueError("dataset privacy check failed")
        for name, data in additions.items():
            if read(name, result.oid) != data:
                raise ValueError("committed data differs from verified evidence")
        return result.oid, root, "published"


def main():
    env = os.environ
    if env.get("HF_OIDC_RESOURCE") != "datasets/" + REPO:
        raise ValueError("expected the dataset's Trusted Publisher identity")
    digest = env["INPUT_SHA256"]
    target = env.get("ATLAS_TARGET", "")
    archive_digest = env["ARTIFACT_DIGEST"].removeprefix("sha256:")
    files = checked_files(Path(sys.argv[1]), archive_digest, digest, target, env["GITHUB_SHA"])
    run = int(env["GITHUB_RUN_ID"])
    files["github-run.json"] = json_bytes({
        "run_url": f"https://github.com/project-numina/mtc/actions/runs/{run}",
        "run_attempt": int(env["GITHUB_RUN_ATTEMPT"]), "artifact_id": int(env["ARTIFACT_ID"]),
        "artifact_digest": "sha256:" + archive_digest, "input_sha256": digest,
        "verifier_commit": env["GITHUB_SHA"],
    })
    revision, folder, status = publish(files, digest, target)
    url = f"https://huggingface.co/datasets/{REPO}/tree/{revision}/{folder}"
    message = f"Submission {status}. [Private dataset entry]({url})"
    with open(env["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
        print(message, file=summary)
    print(message)


if __name__ == "__main__":
    main()
