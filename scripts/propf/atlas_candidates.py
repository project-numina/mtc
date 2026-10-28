#!/usr/bin/env python3
"""Scan checksum-verified Atlas exports for weakly integral candidate data.

Downloads remain in scratch/propf-atlas. Atlas flags are descriptive data, not
proofs of categorification or of weakly group-theoretical status.
"""
import concurrent.futures
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

from sympy import factorint

BASE = "https://anyonatlas.org/export-v1/"
CACHE = Path("scratch/propf-atlas")
INTEGER = re.compile(r"[+-]?\d+\Z")


def fetch(name, checksum=None):
    path = CACHE / name
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        content = subprocess.run(["curl", "--fail", "--silent", "--show-error", "--location",
                                  "--max-time", "60", BASE + name],
                                 check=True, capture_output=True).stdout
        if checksum and hashlib.sha256(content).hexdigest() != checksum:
            raise ValueError(f"checksum mismatch: {name}")
        path.write_bytes(content)
    content = path.read_bytes()
    if checksum and hashlib.sha256(content).hexdigest() != checksum:
        raise ValueError(f"checksum mismatch: {name}")
    return content


def load_chunk(chunk):
    result = []
    for name in ("identifiers-exact", "structure"):
        family = chunk["families"][name]
        obj = json.loads(gzip.decompress(fetch(family["file"], family["sha256"])))
        if obj["family"] != name or len(obj["records"]) != chunk["count"]:
            raise ValueError("unexpected chunk family or count")
        result.append({r["id"]: r for r in obj["records"]})
    if result[0].keys() != result[1].keys() or set(result[0]) != set(chunk["ids"]):
        raise ValueError("chunk identifiers do not match manifest")
    return result


def main():
    manifest = json.loads(fetch("manifest.json"))
    chunks = [c for rank in manifest["kinds"]["bosonic"]["ranks"] for c in rank["chunks"]]
    output = []
    weak = 0
    flagged = []
    unmatched = []
    unflagged_literal_integers = []
    count = 0
    seen = set()
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for exact, structure in pool.map(load_chunk, chunks):
            for id_, entry in exact.items():
                if id_ in seen:
                    raise ValueError(f"duplicate record: {id_}")
                seen.add(id_)
                count += 1
                props = structure[id_]["propertiesRealizations"]
                dim = entry["globalDimensionSquared"]
                if props.get("weaklyIntegral") is not True:
                    if INTEGER.fullmatch(dim):
                        unflagged_literal_integers.append(id_)
                    continue
                weak += 1
                flagged.append({"id": id_, "rank": entry["rank"],
                                "exact_global_dimension": dim,
                                "positive_dimensions": props.get("positiveDimensions")})
                if not INTEGER.fullmatch(dim):
                    unmatched.append({"id": id_, "exact_global_dimension": dim})
                    continue
                if props.get("positiveDimensions") is not True:
                    continue
                eligibility = props.get("chernSimonsEligibility") or {}
                output.append({"id": id_, "rank": entry["rank"], "global_dimension": int(dim),
                               "chern_simons_eligible": eligibility.get("eligible"),
                               "realizations": props.get("realizations", []),
                               "tags": props.get("propertyTags", [])})
    if count != manifest["counts"]["bosonic"]:
        raise ValueError("total bosonic count does not match manifest")
    no_realization = [r for r in output if not r["realizations"]]
    beyond_two_primes = [r for r in no_realization if len(factorint(r["global_dimension"])) > 2]
    print(json.dumps({"source_fingerprint": manifest["sourceFingerprint"],
                      "bosonic_records": manifest["counts"]["bosonic"],
                      "atlas_weakly_integral_flag_count": weak,
                      "atlas_weakly_integral_records": flagged,
                      "flagged_but_nonliteral_exact_dimensions": unmatched,
                      "unflagged_literal_integer_dimensions": unflagged_literal_integers,
                      "positive_row_literal_integral_count": len(output),
                      "positive_row_literal_integral_records": output,
                      "non_cs_eligible": [r for r in output if r["chern_simons_eligible"] is False],
                      "no_recorded_realization": no_realization,
                      "no_recorded_realization_three_or_more_primes": beyond_two_primes}, indent=2))


if __name__ == "__main__":
    main()
