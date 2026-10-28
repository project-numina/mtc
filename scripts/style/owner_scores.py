#!/usr/bin/env python3
"""Report source-style metrics by the cleanup plan's reserved ownership paths.

Run after scripts/style/run.sh for current elaborated-type metrics. Audit modules,
the frozen target and the root import aggregator are excluded from owner scores.
"""

import collections
import csv
from pathlib import Path
import sys

import survey

ROOT = Path(__file__).resolve().parents[2]


def owner(path: Path) -> str:
    parts = path.relative_to(ROOT).parts
    if len(parts) == 2:
        return "cabling"
    if parts[:2] != ("PropertyF", "Ground"):
        raise ValueError(f"No owner for {path}")
    if len(parts) == 3 and parts[2] == "Final.lean":
        return "coord"
    directory = parts[2]
    if directory == "Centre" and len(parts) > 4:
        reserved = {"Induction": "induction", "Calculus": "centre calculus", "Modular": "modularity"}
        if parts[3] in reserved:
            return reserved[parts[3]]
    groups = {
        "Integrate": "coord",
        "Fusion": "fusion", "Dimensions": "fusion",
        "CentreInduction": "induction",
        "CentreCalculus": "centre calculus", "CentreCabling": "centre calculus",
        "CentreModular": "modularity", "CentreDimensions": "modularity",
        "CentreIntegrate": "modularity", "Modular": "modularity",
        "Centre": "centre", "CentreBundle": "centre", "CentreRigid": "centre",
        "Cabling": "cabling", "Calculus": "cabling", "Braid": "cabling", "Trace": "cabling",
    }
    if directory not in groups:
        raise ValueError(f"No owner for {path}")
    return groups[directory]


def metric(values):
    if not values:
        return "n/a"
    q = survey.quant(values)
    return f"{q[1]:g}/{q[3]:g}"


def main():
    entries = collections.defaultdict(list)
    with (ROOT / "STYLE_DECLARATIONS.tsv").open(newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            entries[(row["module"], row["name"].split(".")[-1])].append(row)

    decls = collections.defaultdict(list)
    files = collections.defaultdict(list)
    for path in sorted((ROOT / "PropertyF").rglob("*.lean")):
        if path.name.endswith("Audit.lean") or path == ROOT / "PropertyF/Ground/Target.lean":
            continue
        group = owner(path)
        files[group].append(len(path.read_text().splitlines()))
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for decl in survey.parse(path, module)["declarations"]:
            if decl["kind"] not in ("theorem", "lemma") or not decl["proof_lines"]:
                continue
            match = entries[(module, decl["name"].split(".")[-1])]
            decls[group].append((decl, match[0] if len(match) == 1 else None))

    print("All numeric pairs are median/p90. Type metrics come from the last survey.")
    for group in ("coord", "centre", "centre calculus", "induction", "modularity", "fusion", "cabling"):
        rows = decls[group]
        parsed = [d for d, _ in rows]
        matched = [r for _, r in rows if r and int(r["type_nodes"]) < 999999]
        source = lambda key: metric([d[key] for d in parsed])
        tactics = metric([d["steps"] for d in parsed if d["tactic"]])
        elaborated = lambda key: metric([int(r[key]) for r in matched])
        names = metric([len(d["name"].split(".")[-1]) for d in parsed])
        terms = sum(not d["tactic"] for d in parsed)
        print(f"{group}: files {metric(files[group])} (max {max(files[group])}), "
              f"theorems {len(parsed)}, proof {source('proof_lines')}, tactics {tactics}, "
              f"statement lines {source('statement_lines')}, chars {source('statement_chars')}")
        print(f"  nodes {elaborated('type_nodes')}, binders explicit {elaborated('explicit')}, "
              f"implicit {elaborated('implicit')}, instance {elaborated('instance')}, "
              f"hypotheses {elaborated('hypotheses')}; matched {len(matched)}/{len(parsed)}")
        print(f"  have {source('have')}, simp {source('simp')}, names {names}, "
              f"non-tactic proofs {terms}/{len(parsed)}")
    print("Refresh STYLE_DECLARATIONS.tsv after source changes.", file=sys.stderr)


if __name__ == "__main__":
    main()
