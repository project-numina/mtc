"""Check candidate label maps against the pinned rank-three Anyon Atlas fusion pack."""

import gzip
import hashlib
import itertools
import json
import subprocess

from verify_pentagon import ROOT, table_source


PACK = ROOT / "MTC/AnyonAtlas/bosonic-rank-03-fusion.json.gz"
URL = ("https://anyonatlas.org/data-v2-compact/p-a9cbe6689c07383d/catalog/"
       "bosonic/fusion-packs/03/00000.json.gz")
PACK_SHA256 = "c23e4c73d2e3b5c2a3c658f149600e0ff664b33780606eaff9eed2176b126db7"
FINGERPRINT = "50aa2c6e52b921c12c7f053b352f55cd37afbedb4f394f45a11ddb4b2e948f03"
LABELS = range(3)


def dense_fusion(record):
    # Atlas compact-1 packs enumerate i <= j lexicographically. Each slice
    # stores alternating output labels and positive multiplicities.
    lift, = record["lifts"]
    terms, offsets = lift["terms"], lift["offsets"]
    dense = [0] * 27
    for pair, (i, j) in enumerate(itertools.combinations_with_replacement(LABELS, 2)):
        for pos in range(offsets[pair], offsets[pair + 1], 2):
            k, n = terms[pos:pos + 2]
            dense[9 * i + 3 * j + k] = dense[9 * j + 3 * i + k] = n
    return dense


def label_maps(doc, fusion):
    for p in itertools.permutations(LABELS):
        if p[doc["unit"]] != 0:
            continue
        if all(doc["fusion"][i][j][k] == fusion[9 * p[i] + 3 * p[j] + p[k]]
               for i, j, k in itertools.product(LABELS, repeat=3)):
            yield list(p)


MATCH_PREDICATE = """
abbrev FusionMatch (n : Array Nat) (p : Fin 3 → Fin 3) : Prop :=
  (∀ i j, p i = p j → i = j) ∧
  (∀ j, ∃ i, p i = j) ∧
  (∀ i, i.val = table.unit ↔ (p i).val = 0) ∧
  (∀ i j, table.dual[i.val]?.getD 3 = j.val ↔
    n[9 * (p i).val + 3 * (p j).val]?.getD 0 = 1) ∧
  (∀ i j k, table.mult i.val j.val k.val =
    n[9 * (p i).val + 3 * (p j).val + (p k).val]?.getD 0)
"""


def check_atlas_matches(payload, bundle):
    doc = json.loads(payload)
    if len(doc["dual"]) != 3:
        return None
    packed = PACK.read_bytes()
    if hashlib.sha256(packed).hexdigest() != PACK_SHA256:
        raise ValueError("Atlas fusion pack checksum mismatch")
    records = json.loads(gzip.decompress(packed))["records"]
    header, _, namespace = table_source(payload)
    proof = [header, MATCH_PREDICATE]
    links = []
    for record in records:
        fusion = dense_fusion(record)
        key = record["id"].replace("-", "_")
        maps = list(label_maps(doc, fusion))
        if maps:
            proof.append(f"def fusion_{key} : Array Nat := #{fusion}")
        for p in maps:
            theorem = f"match_{key}_" + "".join(map(str, p))
            proof.append(f"theorem {theorem} : FusionMatch fusion_{key} !{p} := by decide +kernel")
            links.append({"record_id": record["id"], "submission_to_atlas": p,
                          "theorem": f"{namespace}.{theorem}"})
    catalog = {"name": "Anyon Atlas", "source_fingerprint": FINGERPRINT, "url": URL,
               "pack_sha256": PACK_SHA256, "pack_file": PACK.name, "records_examined": len(records)}
    result = {"catalog": catalog, "matches": links}
    (bundle / PACK.name).write_bytes(packed)
    if links:
        path = bundle / "AtlasFusion.lean"
        proof.append(f"end {namespace}\n")
        path.write_text("\n\n".join(proof), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", str(path.resolve())], cwd=ROOT, check=True)
        result["proof"] = path.name
    return result
