#!/usr/bin/env python3
"""Reproduce the earlier survey's metrics for new pivotal modules and Mathlib."""
import argparse
import collections
import csv
import json
import os
from pathlib import Path
import re
import subprocess
from source_metrics import ROOT, STYLE, MATH, parse, mod, sampled, quant, fmt

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--skip-lean", action="store_true")
    args = ap.parse_args()
    out = ROOT / "docs/style"
    out.mkdir(parents=True, exist_ok=True)
    mathpaths = sorted(MATH.rglob("*.lean"))
    sample = [p for p in mathpaths if sampled(mod(p, MATH, "Mathlib"))]
    (STYLE / ".sample-modules").write_text("\n".join(mod(p,MATH,"Mathlib") for p in sample)+"\n")
    if not args.skip_lean:
        imports = "\n".join(re.findall(r"^import all .+$", (ROOT/"MTC/PropertyF/Audit/TargetAudit.lean").read_text(), re.M))
        generated = STYLE/".EnvironmentRun.lean"
        generated.write_text("module\npublic import Mathlib\npublic meta import Lean\n"+imports+"\n"+(STYLE/"Environment.lean").read_text())
        with (out/"environment.log").open("w") as log:
            subprocess.run(["taskset","-c",os.environ.get("PROPERTYF_AUDIT_CORES","0-3"),"lake","env","lean",str(generated)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (STYLE/".environment.tsv").open() as f:
        env=list(csv.DictReader(f,delimiter="\t"))
    bymodule=collections.defaultdict(list)
    for r in env: bymodule[r["module"]].append(r)
    changed=set(subprocess.check_output(["git","diff","--name-only","--diff-filter=AM","56dd74cd","--","MTC"],cwd=ROOT,text=True).splitlines())
    project=[parse(p,mod(p,ROOT/"MTC","MTC")) for p in sorted((ROOT/"MTC").rglob("*.lean"))]
    math=[parse(p,mod(p,MATH,"Mathlib")) for p in sample]
    def attach(fs):
        for f in fs:
            endings=collections.defaultdict(list)
            for r in bymodule[f["module"]]: endings[r["name"].split(".")[-1]].append(r)
            for d in f["declarations"]:
                matches=endings[d["name"].split(".")[-1]]
                if len(matches)==1: d["env"]=matches[0]
    attach(project);attach(math)
    new=[f for f in project if f["file"] in changed]
    old=[f for f in project if f["file"] not in changed]
    groups={"New pivotal modules":new,"Inherited modules":old,"Mathlib sample":math}
    th={k:[d for f in fs for d in f["declarations"] if d["kind"] in ("theorem","lemma") and d["proof_lines"]] for k,fs in groups.items()}
    source=[("Proof lines","proof_lines"),("Tactic steps (by proofs)","steps"),("Statement characters","statement_chars"),("Name characters",None)]
    elaborated=[("Explicit binders","explicit"),("Implicit binders","implicit"),("Instance binders","instance"),("Hypotheses","hypotheses"),("Elaborated type nodes","type_nodes")]
    metrics={}
    for title,key in source:
        metrics[title]={k:[len(d["name"]) if key is None else d[key] for d in ds if title!="Tactic steps (by proofs)" or d["tactic"]] for k,ds in th.items()}
    for title,key in elaborated:
        metrics[title]={k:[int(d["env"][key]) for d in ds if "env" in d and int(d["env"][key])!=999999] for k,ds in th.items()}
    metrics["File lines"]={k:[f["lines"] for f in fs] for k,fs in groups.items()}
    metrics["File lines"]["Mathlib all files"]=[sum(1 for _ in p.open()) for p in mathpaths]
    summary={metric:{k:{"n":len(v),"p25":quant(v)[0],"median":quant(v)[1],"p75":quant(v)[2],"p90":quant(v)[3],"p99":quant(v)[4],"max":quant(v)[5]} for k,v in populations.items()} for metric,populations in metrics.items()}
    (out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    lines=["# Pivotal code distribution audit","", "Survey baseline: original completed pivotal proof, `9c2484eb`; new modules are those added or modified since `56dd74cd`. Current working tree is measured. Historical methodology: `property-f-style/scripts/style/survey.py`, copied into this repository as `source_metrics.py`. Lean/Mathlib v4.35.0.","",
    "Source parsing and tactic counts are lexical estimates; binders and hypotheses come from Lean's elaborated types, including section variables. Only unique module-local terminal-name matches are retained. Hypothesis sentinel failures are omitted. Quantiles use linear interpolation. The Mathlib sample is the same deterministic SHA-256(module) mod 10 = 0 sample as the previous survey; it is unstratified and is not a category-theory-only benchmark. New-module statistics include helper declarations, not just the final theorem.","",
    "| Population | Files | Source theorems | Matched to Lean |","|---|---:|---:|---:|"]
    for k,fs in groups.items():lines.append(f"| {k} | {len(fs)} | {len(th[k])} | {sum('env' in d for d in th[k])} |")
    lines+=["","## Assessment","",
    "The new proof layer is longer and more fragmented than the inherited cleaned library: proof-line median/p90 are 6/20 versus 3/12; explicit-binder median/p90 are 3/7 versus 2/5; file-line median is 67 versus 145. These are descriptive differences, not a statistical test or evidence of incorrectness.",
    "Hypothesis median/p90 (1/3) matches the Mathlib sample, so a blanket reduction in assumptions is not indicated. Prioritize coherent consolidation of the many small cabling, trace and reduction modules, then review the longest proofs for mathematical reuse and explicit parameters that Lean can infer naturally.",
    "Keep the final theorem entry points short and readable. Any future refactoring must preserve exact statements, complete library builds, the statement-equivalence check and the axiom audits. Matching Mathlib quantiles is not itself a completion criterion.","",
    f"Of {len(th['New pivotal modules'])} matched new source theorems, {sum(d['env']['cone']=='1' for d in th['New pivotal modules'] if 'env' in d)} occur in the constant-reference dependency union of the six manuscript targets and {sum(d['env']['cone']=='0' for d in th['New pivotal modules'] if 'env' in d)} do not. The latter are review candidates, not safe automatic deletions: elaboration, attributes, instances and reusable public APIs require separate inspection.","",
    "The old October 27 survey had proof-line median/p90 8/26 and 509 files before the earlier cleanup. The relevant regression comparison here is the current inherited library, not that pre-cleanup snapshot.","",
    "## Distributions","","| Metric | Population | n | p25 | Median | p75 | p90 | p99 | Max |","|---|---|---:|---:|---:|---:|---:|---:|---:|"]
    for metric,pop in metrics.items():
        for k,v in pop.items():lines.append("| "+metric+" | "+k+" | "+str(len(v))+" | "+" | ".join(map(fmt,quant(v)))+" |")
    lines+=["","## Review candidates","","These are review priorities, not automatic refactoring requirements. Do not change mathematical statements, hide assumptions, or split proofs into trivial wrappers to fit a distribution.","","Longest new proofs:",""]
    for d in sorted(th["New pivotal modules"],key=lambda d:-d["proof_lines"])[:20]:
        lines.append(f"- `{d['file']}:{d['line']}` `{d['name']}`: {d['proof_lines']} lines, {d['steps']} estimated tactic steps.")
    lines+=["","Largest explicit-binder counts among matched new theorems:",""]
    for d in sorted([d for d in th["New pivotal modules"] if "env" in d],key=lambda d:-int(d["env"]["explicit"]))[:15]:
        lines.append(f"- `{d['file']}:{d['line']}` `{d['name']}`: {d['env']['explicit']} explicit, {d['env']['implicit']} implicit, {d['env']['instance']} instance binders.")
    lines+=["","## Reproduction","","`LEAN_NUM_THREADS=4 python3 scripts/style/survey.py` regenerates this report, project source scorecards and summary statistics. Intermediate elaborated data is git-ignored. `--skip-lean` reuses the existing environment dump and must not be used after changing declarations.",""]
    (out/"README.md").write_text("\n".join(lines))
    ds=[{"population":k,**{key:d.get(key) for key in ("file","line","name","proof_lines","steps","statement_chars")},**{key:d.get("env",{}).get(key,"") for key in ("explicit","implicit","instance","hypotheses","type_nodes","cone")}} for k,decls in th.items() if k != "Mathlib sample" for d in decls]
    with (out/"theorems.tsv").open("w") as f:
        w=csv.DictWriter(f,fieldnames=list(ds[0]),delimiter="\t",lineterminator="\n");w.writeheader();w.writerows(ds)
    with (out/"files.tsv").open("w") as f:
        w=csv.writer(f,delimiter="\t",lineterminator="\n");w.writerow(["population","file","lines","declarations"])
        for k,fs in groups.items():
            for data in fs:w.writerow([k,data["file"],data["lines"],len(data["declarations"])])
    print(json.dumps({m:summary[m] for m in ["Proof lines","Explicit binders","File lines"]},indent=2))
if __name__=="__main__":main()
