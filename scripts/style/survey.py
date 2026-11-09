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

def match_cohort(baseline, current):
    """Pair only unique elaborated identities, independent of source paths."""
    cohort = {d["qualified_name"]: d for d in baseline}
    if len(cohort) != len(baseline) or "" in cohort:
        raise ValueError("baseline cohort has missing or duplicate names")
    byname = collections.defaultdict(list)
    for d in current:
        if "env" in d:
            byname[d["env"]["name"]].append(d)
    pairs = [(d, byname[d["qualified_name"]][0]) for d in baseline
             if len(byname[d["qualified_name"]]) == 1]
    paired_names = {d["qualified_name"] for d, _ in pairs}
    paired_objects = {id(d) for _, d in pairs}
    return (pairs, [d for d in baseline if d["qualified_name"] not in paired_names],
            [d for d in current if id(d) not in paired_objects])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--skip-lean", action="store_true")
    args = ap.parse_args()
    out = ROOT / "docs/style"
    out.mkdir(parents=True, exist_ok=True)
    mathpaths = sorted(MATH.rglob("*.lean"))
    sample = [p for p in mathpaths if sampled(mod(p, MATH, "Mathlib"))]
    sample_modules = [mod(p, MATH, "Mathlib") for p in sample]
    pinned_sample = (out / "mathlib-sample-v4.35.0.txt").read_text().splitlines()
    if sample_modules != pinned_sample:
        raise RuntimeError("Mathlib sample differs from the pinned v4.35.0 sample")
    (STYLE / ".sample-modules").write_text("\n".join(sample_modules)+"\n")
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
    with (out / "cohort-fb6ec518.tsv").open() as f:
        baseline = list(csv.DictReader(f, delimiter="\t"))
    with (out / "cohort-files-fb6ec518.tsv").open() as f:
        baseline_files = list(csv.DictReader(f, delimiter="\t"))
    current = [d for f in project for d in f["declarations"]
               if d["kind"] in ("theorem", "lemma") and d["proof_lines"]]
    pairs, missing, extra = match_cohort(baseline, current)
    # Files are a separate snapshot, not a paired population: deleted baseline
    # paths and newly introduced paths must be disclosed explicitly.
    file_population = {r["file"]: r["population"] for r in baseline_files
                       if r["population"] != "Mathlib sample"}
    new = [f for f in project if file_population.get(f["file"]) == "New pivotal modules"]
    old = [f for f in project if file_population.get(f["file"]) == "Inherited modules"]
    unclassified_files = [f["file"] for f in project if f["file"] not in file_population]
    current_paths = {f["file"] for f in project}
    deleted_files = [path for path in file_population if path not in current_paths]
    groups = {"New pivotal modules": new, "Inherited modules": old, "Mathlib sample": math}
    th = {k: [after for before, after in pairs if before["population"] == k]
          for k in ("New pivotal modules", "Inherited modules")}
    th["Mathlib sample"] = [d for f in math for d in f["declarations"]
                            if d["kind"] in ("theorem", "lemma") and d["proof_lines"]]
    with (out / "cohort-unmatched.tsv").open("w") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(["kind", "file", "line", "name", "qualified_name"])
        for d in missing: w.writerow(["baseline unmatched", d["file"], d["line"], d["name"], d["qualified_name"]])
        for d in extra: w.writerow(["current unpaired", d["file"], d["line"], d["name"], d.get("env", {}).get("name", "")])
    source=[("Proof lines","proof_lines"),("Tactic steps (by proofs)","steps"),("Statement characters","statement_chars"),("Name characters",None)]
    elaborated=[("Explicit binders","explicit"),("Implicit binders","implicit"),("Instance binders","instance"),("Hypotheses","hypotheses"),("Elaborated type nodes","type_nodes")]
    metrics={}
    for title,key in source:
        metrics[title]={k:[len(d["name"]) if key is None else d[key] for d in ds if title!="Tactic steps (by proofs)" or d["tactic"]] for k,ds in th.items()}
    for title,key in elaborated:
        metrics[title]={k:[int(d["env"][key]) for d in ds if "env" in d and int(d["env"][key])!=999999] for k,ds in th.items()}
    for title, key in source + elaborated:
        for population in ("New pivotal modules", "Inherited modules"):
            label = population + " (fb6ec518 paired)"
            rows = [before for before, after in pairs if before["population"] == population]
            if title == "Tactic steps (by proofs)":
                # The old scorecard does not record whether a proof used `by`.
                # Its tactic-step population cannot be reconstructed faithfully.
                continue
            if title == "Name characters":
                metrics[title][label] = [len(d["name"]) for d in rows]
            elif key:
                metrics[title][label] = [int(d[key]) for d in rows if d[key] and d[key] != "999999"]
    metrics["File lines"]={k:[f["lines"] for f in fs] for k,fs in groups.items()}
    metrics["File lines"]["Mathlib all files"]=[sum(1 for _ in p.open()) for p in mathpaths]
    summary={metric:{k:{"n":len(v),"p25":quant(v)[0],"median":quant(v)[1],"p75":quant(v)[2],"p90":quant(v)[3],"p99":quant(v)[4],"max":quant(v)[5]} for k,v in populations.items()} for metric,populations in metrics.items()}
    (out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    lines=["# Pivotal code distribution audit", "",
    "The [second-pass target dashboard](target-report.md) expands the source census, pins both original and round-two cohorts, and reports the explicit acceptance targets and complete outliers. The historical comparison below retains its original parser for continuity.", "",
    "The declaration cohort is pinned by fully qualified Lean name at `fb6ec518`, using the then-current survey's module-local, unique terminal-name matches. Current and baseline theorem statistics use only successfully paired declarations; module moves with unchanged public names remain in the cohort. Missing, renamed, private-name changes and newly added or source-unmatched declarations appear in [cohort-unmatched.tsv](cohort-unmatched.tsv); they are not silently counted as improvements. The complete original baseline is [preserved separately](historical-fb6ec518.md).", "",
    "Proof lines and tactic steps are source-parser heuristics, not elaborated proof size; binder and hypothesis counts come from Lean elaborated types, including section variables. Terminal-name matching is module-local and requires uniqueness. Hypothesis sentinel failures are omitted. Quantiles use linear interpolation. The pinned Mathlib v4.35.0 sample uses SHA-256(module) mod 10 = 0 and is unstratified, not category-theory-specific. Mathlib source and Lean-match counts differ; unmatched source declarations are retained in source metrics only.", "",
    "| Population | Current files | Source theorems (project paired) | Matched to Lean |", "|---|---:|---:|---:|"]
    for k, fs in groups.items():
        lines.append(f"| {k} | {len(fs)} | {len(th[k])} | {sum('env' in d for d in th[k])} |")
    lines += ["", "## Assessment", ""]
    def comparison(metric, pop):
        current_q = summary[metric][pop]
        before_q = summary[metric][pop + " (fb6ec518 paired)"]
        return f"{fmt(before_q['median'])}/{fmt(before_q['p90'])} → {fmt(current_q['median'])}/{fmt(current_q['p90'])}"
    lines += [f"For the {len(th['New pivotal modules'])} paired new-layer declarations, source proof-line median/p90 changed {comparison('Proof lines', 'New pivotal modules')}; elaborated explicit binders changed {comparison('Explicit binders', 'New pivotal modules')}. These describe the surviving matched cohort, not the effect of deleted or unpaired declarations.",
    f"There are {len(missing)} unmatched baseline declarations and {len(extra)} unpaired current source declarations. The file distribution is a snapshot of surviving baseline paths, not a paired declaration metric: {len(deleted_files)} baseline project paths are absent and {len(unclassified_files)} current project paths are unclassified. Names are listed below.",
    "Cohort changes require source, consumer, instance, attribute and supported-API review; dependency reachability alone is not a deletion criterion. [Cleanup decisions and retained exceptions](cleanup-notes.md) document the review. The explicit targets for the second pass and their status are reported in the target dashboard.", "",
    f"Among paired new declarations, {sum(d['env']['cone']=='1' for d in th['New pivotal modules'])} occur in the current constant-reference dependency union of the six manuscript targets and {sum(d['env']['cone']=='0' for d in th['New pivotal modules'])} do not. This is a review aid, not a safe deletion list.", "",
    "## Distributions", "", "Paired baseline rows use the exact same qualified names as their current rows. The historical tactic-step distribution cannot be paired because the old scorecard did not retain the `by`-proof flag. File counts are not paired.", "", "| Metric | Population | n | p25 | Median | p75 | p90 | p99 | Max |", "|---|---|---:|---:|---:|---:|---:|---:|"]
    for metric,pop in metrics.items():
        for k,v in pop.items():lines.append("| "+metric+" | "+k+" | "+str(len(v))+" | "+" | ".join(map(fmt,quant(v)))+" |")
    lines+=["","## Review candidates","","These are review priorities, not automatic refactoring requirements. Do not change mathematical statements, hide assumptions, or split proofs into trivial wrappers to fit a distribution.","","Longest new proofs:",""]
    for d in sorted(th["New pivotal modules"],key=lambda d:-d["proof_lines"])[:20]:
        lines.append(f"- `{d['file']}:{d['line']}` `{d['name']}`: {d['proof_lines']} lines, {d['steps']} estimated tactic steps.")
    lines+=["","Largest explicit-binder counts among matched new theorems:",""]
    for d in sorted([d for d in th["New pivotal modules"] if "env" in d],key=lambda d:-int(d["env"]["explicit"]))[:15]:
        lines.append(f"- `{d['file']}:{d['line']}` `{d['name']}`: {d['env']['explicit']} explicit, {d['env']['implicit']} implicit, {d['env']['instance']} instance binders.")
    lines += ["", "## File cohort changes", "", "Absent baseline paths:"]
    lines += [f"- `{path}`" for path in deleted_files] or ["- None."]
    lines += ["", "Unclassified current paths:"]
    lines += [f"- `{path}`" for path in unclassified_files] or ["- None."]
    lines += ["", "## Reproduction", "", "`LEAN_NUM_THREADS=4 python3 scripts/style/survey.py` regenerates this report, scorecards and summary statistics. Build the project first. Intermediate elaborated data is git-ignored. `--skip-lean` reuses the existing environment dump and must not be used after changing declarations.", ""]
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
