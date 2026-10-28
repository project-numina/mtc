#!/usr/bin/env python3
"""Check named project declarations against the last target-cone survey.

Run scripts/style/run.sh first. Instances, notation and attributes are excluded:
they can be needed during elaboration even without a named proof dependency.
Audit modules and the frozen target are excluded from the deletion check.
"""

import collections
import csv
from pathlib import Path

import survey

ROOT = Path(__file__).resolve().parents[2]
KINDS = {"def", "abbrev", "theorem", "lemma", "opaque"}


def main():
    entries = collections.defaultdict(list)
    with (ROOT / "STYLE_DECLARATIONS.tsv").open(newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            entries[(row["module"], row["name"].split(".")[-1])].append(row)

    outside = []
    unmatched = []
    for path in sorted((ROOT / "PropertyF").rglob("*.lean")):
        if path.name.endswith("Audit.lean") or path == ROOT / "PropertyF/Ground/Target.lean":
            continue
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for decl in survey.parse(path, module)["declarations"]:
            if decl["kind"] not in KINDS:
                continue
            name = decl["name"].split(".")[-1]
            matches = entries[(module, name)]
            if len(matches) != 1:
                unmatched.append((path.relative_to(ROOT), name, len(matches)))
            elif matches[0]["cone"] == "0":
                outside.append((path.relative_to(ROOT), name))

    for path, name in outside:
        print(f"Outside target cone: {path}: {name}")
    for path, name, count in unmatched:
        print(f"Unmatched or ambiguous ({count}): {path}: {name}")
    print(f"Outside cone: {len(outside)}; unmatched or ambiguous: {len(unmatched)}.")
    return bool(outside or unmatched)


if __name__ == "__main__":
    raise SystemExit(main())
