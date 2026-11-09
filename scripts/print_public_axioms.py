#!/usr/bin/env python3
"""Print and check axioms of uniquely matched public project source theorems.

Run the fresh style survey first, after building the project. The independent
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
    names, unmatched = set(), []
    for path in sorted((ROOT / 'MTC').rglob('*.lean')):
        module = mod(path, ROOT / 'MTC', 'MTC')
        for d in parse(path, module)['declarations']:
            if d['kind'] not in ('theorem', 'lemma') or not d['proof_lines']:
                continue
            matches = index[(module, d['name'].split('.')[-1])]
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
    print(f'Explicit axiom outputs checked: {len(names)} public source theorems.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
