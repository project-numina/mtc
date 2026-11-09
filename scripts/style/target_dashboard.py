#!/usr/bin/env python3
"""Account for both pinned theorem cohorts and all current new-layer source proofs.

Run after a fresh survey, or with --pin-round-two only at 3826bb02. Source
parsing and module-local matching deliberately use the survey's heuristics.
"""
import argparse
import collections
import csv
import json
import re
import subprocess
from pathlib import Path
from source_metrics import ROOT, STYLE, parse, mod, quant

OUT = ROOT / 'docs/style'
FIELDS = ['population', 'file', 'line', 'kind', 'name', 'qualified_name', 'match',
          'proof_lines', 'tactic', 'steps', 'explicit', 'implicit', 'strict',
          'instance', 'hypotheses']

def read(path):
    with path.open(newline='') as f:
        return list(csv.DictReader(f, delimiter='\t'))

def write(path, rows, fields):
    with path.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fields, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerows(rows)

def snapshot():
    env = collections.defaultdict(list)
    for e in read(STYLE / '.environment.tsv'):
        if e['module'].startswith('MTC.') and e['kind'] in ('theorem', 'axiom'):
            env[(e['module'], e['name'].split('.')[-1])].append(e)
    anonymous_env = collections.defaultdict(list)
    for (module, terminal), hits in env.items():
        if terminal.startswith('inst'):
            anonymous_env[module].extend(hits)
    files = {r['file']: r['population'] for r in read(OUT / 'cohort-files-fb6ec518.tsv')}
    original = read(OUT / 'cohort-fb6ec518-expanded.tsv')
    old_names = {r['qualified_name'] for r in original if r['population'] == 'Inherited modules'}
    rows = []
    for path in sorted((ROOT / 'MTC').rglob('*.lean')):
        module = mod(path, ROOT / 'MTC', 'MTC')
        for d in parse(path, module, include_inline_attributes=True, count_all_proofs=True)['declarations']:
            if not d['proof_lines']:
                continue
            hits = (anonymous_env[module] if d['name'] == '(anonymous)'
                    else env[(module, d['name'].split('.')[-1])])
            e = hits[0] if len(hits) == 1 else {}
            if d['kind'] not in ('theorem', 'lemma') and not e:
                continue
            population = files.get(d['file'], 'New pivotal modules')
            # Declarations added to inherited files are included. Ambiguous names
            # stay in the accounting instead of silently disappearing.
            if population == 'Inherited modules' and e.get('name') not in old_names:
                population = 'New pivotal modules (in inherited file; review)'
            rows.append(dict(population=population, file=d['file'], line=d['line'], kind=d['kind'], name=d['name'],
                             qualified_name=e.get('name', ''), match=('unique' if e else 'missing' if not hits else 'ambiguous'),
                             proof_lines=d['proof_lines'], tactic=int(d['tactic']), steps=d['steps'],
                             **{k: e.get(k, '') for k in ('explicit', 'implicit', 'strict', 'instance', 'hypotheses')}))
    return rows

def metrics(rows):
    result = {'n': len(rows)}
    for key in ('proof_lines', 'steps', 'explicit', 'implicit', 'strict', 'instance', 'hypotheses'):
        vals = [int(r[key]) for r in rows if r.get(key, '') != '' and r[key] != '999999'
                and (key != 'steps' or str(r.get('tactic', '')) == '1')]
        result[key] = {'n': len(vals), 'sum': sum(vals), 'p25_median_p75_p90_p99_max': quant(vals)}
    total = [sum(int(r[k]) for k in ('explicit', 'implicit', 'strict', 'instance')) for r in rows
             if all(r.get(k, '') != '' for k in ('explicit', 'implicit', 'strict', 'instance'))]
    result['total_binders'] = {'n': len(total), 'sum': sum(total), 'p25_median_p75_p90_p99_max': quant(total)}
    return result

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pin-round-two', action='store_true')
    args = ap.parse_args()
    current = snapshot()
    pin = OUT / 'cohort-3826bb02.tsv'
    if args.pin_round_two:
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True, cwd=ROOT).strip()
        if head != '3826bb021a6e1ffea30cf9e86fa3bb06eb13967d':
            raise SystemExit('round-two pin requires exact 3826bb02 HEAD')
        write(pin, current, FIELDS)
    round_two = read(pin)
    original = read(OUT / 'cohort-fb6ec518-expanded.tsv')
    legacy = read(OUT / 'cohort-fb6ec518-full.tsv')
    all_new = [r for r in current if r['population'].startswith('New pivotal modules')]
    write(OUT / 'all-new-proofs.tsv', all_new, FIELDS)
    # Environment-only theorems are retained for review: most are generated
    # equation lemmas, tactic auxiliaries, or recursors, not source commands.
    modules = {r['file'][:-5].replace('/', '.') for r in all_new}
    matched = {r['qualified_name'] for r in all_new if r['qualified_name']}
    generated = re.compile(r'(?:\.(?:_proof_\d|_simp_\d|match_\d|eq_\d|eq_def|congr_simp|_eq_\d)|\._sunfold|\.injEq|\.ext_iff|\.ext$|\.noConfusion|\.casesOn|\.recOn|\.brecOn)')
    environment_only = []
    for row in read(STYLE / '.environment.tsv'):
        if row['module'] in modules and row['kind'] == 'theorem' and row['name'] not in matched:
            row['classification'] = 'generated-name pattern' if generated.search(row['name']) else 'review'
            environment_only.append(row)
    environment_only.sort(key=lambda row: (row['module'], row['name']))
    if environment_only:
        write(OUT / 'environment-only-theorems.tsv', environment_only,
              ['classification'] + list(read(STYLE / '.environment.tsv')[0]))
    results = {'all_current_new': metrics(all_new), 'matching_audit': {
        'source_unmatched': sum(r['match'] != 'unique' for r in all_new),
        'environment_only': len(environment_only),
        'environment_only_review': sum(r['classification'] == 'review' for r in environment_only)}}
    index = collections.defaultdict(list)
    for row in current:
        if row['qualified_name']:
            index[row['qualified_name']].append(row)
    unmatched = []
    for label, base in (('fb6ec518_legacy', legacy), ('fb6ec518', original), ('3826bb02', round_two)):
        base = [r for r in base if r['population'].startswith('New pivotal modules')]
        pairs = []
        for b in base:
            name = b.get('qualified_name', '')
            hits = index[name] if name else []
            if len(hits) == 1:
                pairs.append((b, hits[0]))
            else:
                unmatched.append({'cohort': label, 'kind': 'baseline unmatched', **b})
        used = {id(c) for _, c in pairs}
        for c in all_new:
            if id(c) not in used:
                unmatched.append({'cohort': label, 'kind': 'current unpaired', **c})
        # Original pinned scorecard lacks by-proof flags and strict binders.
        results[label] = {'paired': len(pairs), 'before': metrics([b for b, _ in pairs]),
                          'after': metrics([c for _, c in pairs])}
    write(OUT / 'target-unmatched.tsv', unmatched, ['cohort', 'kind'] + FIELDS)
    (OUT / 'target-dashboard.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))

if __name__ == '__main__':
    main()
