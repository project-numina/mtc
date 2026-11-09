#!/usr/bin/env python3
"""Print and check axioms of matched public project source proofs.

Run the fresh style survey and proposition-definition scan first, after building
the project. The independent
kernel-environment audit in check.sh covers every project declaration, including
private declarations and names that the source heuristic cannot match.
"""
import collections
import csv
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts/style'))
from source_metrics import parse, mod


def main():
    with (ROOT / 'scripts/style/.environment.tsv').open() as f:
        env = list(csv.DictReader(f, delimiter='\t'))
    index = collections.defaultdict(list)
    for d in env:
        index[(d['module'], d['name'].split('.')[-1])].append(d['name'])
    proof_names = {(d['module'], d['name']) for d in env if d['kind'] in ('theorem', 'axiom')}
    with (ROOT / 'scripts/style/.proposition-definitions.tsv').open() as f:
        proof_names.update((d['module'], d['name']) for d in csv.DictReader(f, delimiter='\t'))
    names, unmatched = set(), []
    anonymous = collections.defaultdict(list)
    for d in env:
        if (d['module'], d['name']) in proof_names and d['name'].split('.')[-1].startswith('inst'):
            anonymous[d['module']].append(d['name'])
    for path in sorted((ROOT / 'MTC').rglob('*.lean')):
        module = mod(path, ROOT / 'MTC', 'MTC')
        for d in parse(path, module, include_inline_attributes=True, count_all_proofs=True)['declarations']:
            if not d['proof_lines']:
                continue
            if d['name'] == '(anonymous)':
                matches = anonymous[module]
            else:
                matches = index[(module, d['name'].split('.')[-1])]
            # Non-theorem source declarations include data definitions and
            # ordinary instances. Include only Lean proposition-valued matches.
            if d['kind'] not in ('theorem', 'lemma'):
                matches = [n for n in matches if (module, n) in proof_names]
                if not matches:
                    continue
            if d['name'] == '(anonymous)' and len(matches) > 1:
                names.update(n for n in matches if not n.startswith('_private.'))
                continue
            if len(matches) != 1:
                unmatched.append(f"{d['file']}:{d['line']} {d['name']}")
            elif not matches[0].startswith('_private.'):
                names.add(matches[0])
    # The unmatched list is an explicit failure; the broader audit remains a
    # separate safeguard for all declarations and non-source-generated names.
    if unmatched:
        print('Unmatched source theorems:\n' + '\n'.join(unmatched), file=sys.stderr)
        return 1
    source = 'import MTC\n' + ''.join(f'#print axioms {name}\n' for name in sorted(names))
    scratch = ROOT / 'scratch'
    scratch.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', suffix='.lean', dir=scratch, delete=False) as f:
        f.write(source)
        filename = f.name
    try:
        result = subprocess.run(['taskset', '-c', os.environ.get('PROPERTYF_AUDIT_CORES', '0-3'),
                                 'lake', 'env', 'lean', filename], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    finally:
        os.unlink(filename)
    print(result.stdout, end='')
    if result.returncode:
        return result.returncode
    outputs = re.findall(r"'([^\n]+?)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", result.stdout)
    if len(outputs) != len(names) or {name for name, _ in outputs} != names:
        print(f'Expected {len(names)} distinct outputs, got {len(outputs)}', file=sys.stderr)
        return 1
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in outputs:
        unexpected = set(filter(None, (a.strip() for a in axioms.split(',')))) - allowed
        if unexpected:
            print(f'{name}: unexpected axioms {sorted(unexpected)}', file=sys.stderr)
            return 1
    print(f'Explicit axiom outputs checked: {len(names)} public source proofs.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
