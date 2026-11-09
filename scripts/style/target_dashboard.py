#!/usr/bin/env python3
"""Account for both pinned theorem cohorts and all current new-layer source proofs.

Run after a fresh survey, or with --pin-round-two only at 3826bb02. Source
parsing and module-local matching deliberately use the survey's heuristics.
"""
import argparse
import collections
import csv
import json
import math
import re
import subprocess
from pathlib import Path
from source_metrics import ROOT, STYLE, parse, mod, quant

OUT = ROOT / 'docs/style'
FIELDS = ['population', 'file', 'line', 'kind', 'name', 'qualified_name', 'match',
          'proof_lines', 'tactic', 'steps', 'explicit', 'implicit', 'strict',
          'instance', 'hypotheses', 'type_hash']

def read(path):
    with path.open(newline='') as f:
        return list(csv.DictReader(f, delimiter='\t'))

def write(path, rows, fields):
    with path.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fields + ['_end'], delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerows({**row, '_end': '-'} for row in rows)

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
    old_names = {r['qualified_name'] for r in original if r['population'] == 'Inherited modules' and r['qualified_name']}
    old_sources = {(r['file'], str(r['line']), r['kind'], r['name']) for r in original
                   if r['population'] == 'Inherited modules'}
    rows = []
    for path in sorted((ROOT / 'MTC').rglob('*.lean')):
        module = mod(path, ROOT / 'MTC', 'MTC')
        for d in parse(path, module, include_inline_attributes=True, count_all_proofs=True)['declarations']:
            if not d['proof_lines']:
                continue
            hits = (anonymous_env[module] if d['name'] == '(anonymous)'
                    else env[(module, d['name'].split('.')[-1])])
            e = hits[0] if len(hits) == 1 else {}
            if d['kind'] not in ('theorem', 'lemma') and not hits:
                continue
            population = files.get(d['file'], 'New pivotal modules')
            # Declarations added to inherited files are included. Ambiguous names
            # stay in the accounting instead of silently disappearing.
            if (population == 'Inherited modules' and e.get('name') not in old_names
                and (d['file'], str(d['line']), d['kind'], d['name']) not in old_sources):
                population = 'New pivotal modules (in inherited file; review)'
            rows.append(dict(population=population, file=d['file'], line=d['line'], kind=d['kind'], name=d['name'],
                             qualified_name=e.get('name', ''), match=('unique' if e else 'missing' if not hits else 'ambiguous'),
                             proof_lines=d['proof_lines'], tactic=int(d['tactic']), steps=d['steps'],
                             **{k: e.get(k, '') for k in ('explicit', 'implicit', 'strict', 'instance', 'hypotheses', 'type_hash')}))
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

def target_gap(values, percentile, target, minimum):
    """Lower bound on changes at fixed population, allowing arbitrary reductions.

    The estimate ignores mathematical and API constraints. It considers the
    same interpolation as the survey, including ties at the two order stats.
    """
    values = sorted(values)
    if not values:
        return None
    position = (len(values) - 1) * percentile
    lo, hi = math.floor(position), math.ceil(position)
    weight = position - lo
    def best_after(changes):
        def at(index):
            return values[index - changes] if index >= changes else minimum
        return at(lo) * (1 - weight) + at(hi) * weight
    changes = next(k for k in range(len(values) + 1) if best_after(k) <= target)
    return {'n': len(values), 'target': target,
            'boundary_positions_one_based': [lo + 1, hi + 1],
            'boundary_values': [values[lo], values[hi]],
            'at_or_below_target': sum(v <= target for v in values),
            'equal_to_target': sum(v == target for v in values),
            'above_target': sum(v > target for v in values),
            'minimum_distinct_reductions_relaxed': changes}

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
    outliers = [r for r in all_new if int(r['proof_lines']) > 12
                or (r['explicit'] and int(r['explicit']) > 5)
                or (r['hypotheses'] and r['hypotheses'] != '999999'
                    and int(r['hypotheses']) > 3)]
    write(OUT / 'target-outliers.tsv', outliers, FIELDS)
    # Environment-only theorems are retained for review: most are generated
    # equation lemmas, tactic auxiliaries, or recursors, not source commands.
    classified = {r['file']: r['population'] for r in read(OUT / 'cohort-files-fb6ec518.tsv')}
    modules = {mod(p, ROOT / 'MTC', 'MTC') for p in (ROOT / 'MTC').rglob('*.lean')
               if classified.get(str(p.relative_to(ROOT)), 'New pivotal modules') == 'New pivotal modules'}
    modules.update(r['file'][:-5].replace('/', '.') for r in all_new)
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
    results['target_gaps'] = {}
    for key, percentile, target, minimum in (
            ('proof_lines', .5, 3, 1), ('proof_lines', .9, 12, 1),
            ('explicit', .5, 2, 0), ('explicit', .9, 5, 0)):
        values = [int(r[key]) for r in all_new if r.get(key, '') not in ('', '999999')]
        results['target_gaps'][f'{key}_p{int(percentile * 100)}'] = {
            'missing': len(all_new) - len(values),
            **(target_gap(values, percentile, target, minimum) or {})}
    middle = collections.Counter(r['file'] for r in all_new if 4 <= int(r['proof_lines']) <= 12)
    results['middle_proofs_by_file'] = [
        {'file': file, 'count': count} for file, count in middle.most_common()]
    index = collections.defaultdict(list)
    for row in current:
        if row['qualified_name']:
            index[row['qualified_name']].append(row)
    unmatched = []
    changed_types = []
    for label, base in (('fb6ec518_legacy', legacy), ('fb6ec518', original), ('3826bb02', round_two)):
        base = [r for r in base if r['population'].startswith('New pivotal modules')]
        pairs = []
        for b in base:
            name = b.get('qualified_name', '')
            hits = index[name] if name else []
            if len(hits) == 1:
                pairs.append((b, hits[0]))
            else:
                unmatched.append({'cohort': label, 'status': 'baseline unmatched', **b})
        used = {id(c) for _, c in pairs}
        for c in all_new:
            if id(c) not in used:
                unmatched.append({'cohort': label, 'status': 'current unpaired', **c})
        for b, c in pairs:
            if b.get('type_hash') and c.get('type_hash') and b['type_hash'] != c['type_hash']:
                changed_types.append({'cohort': label, 'qualified_name': b['qualified_name'],
                                      'before_hash': b['type_hash'], 'after_hash': c['type_hash'],
                                      'before_file': b['file'], 'after_file': c['file']})
        results[label] = {'paired': len(pairs), 'before': metrics([b for b, _ in pairs]),
                          'after': metrics([c for _, c in pairs])}
    write(OUT / 'target-unmatched.tsv', unmatched, ['cohort', 'status'] + FIELDS)
    write(OUT / 'target-type-hash-changes.tsv', changed_types,
          ['cohort', 'qualified_name', 'before_hash', 'after_hash', 'before_file', 'after_file'])
    def area(row):
        file = row['file']
        if file.startswith('MTC/Braided/Cabling/'):
            return 'cabling'
        if (file.startswith('MTC/Center/Normalization/') or
            file in ('MTC/Center/Induction/PivotalFusion.lean',
                     'MTC/Center/Induction/PivotalSquare.lean')):
            return 'centre'
        if (file.startswith('MTC/Braided/Trace/') or file.startswith('MTC/Algebra/')):
            return 'trace and algebra'
        if file.startswith('MTC/PropertyF/Pivotal/') and any(
            Path(file).name.startswith(prefix) for prefix in
            ('Nondegeneracy', 'Slope', 'Monoidal', 'FPObject', 'FPGlobalDimension',
             'SOrthogonality', 'Galois')):
            return 'infrastructure'
        return 'other new layer'
    results['areas'] = {}
    for label in sorted({area(r) for r in all_new} | {area(r) for r in round_two
                         if r['population'].startswith('New pivotal modules')}):
        before = [r for r in round_two if r['population'].startswith('New pivotal modules')
                  and area(r) == label]
        after = [r for r in all_new if area(r) == label]
        results['areas'][label] = {'round_two_all': metrics(before),
                                  'current_all': metrics(after)}
    (OUT / 'target-dashboard.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))

if __name__ == '__main__':
    main()
