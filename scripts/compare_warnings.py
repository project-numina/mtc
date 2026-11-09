#!/usr/bin/env python3
"""Compare cached Lean trace warnings with a saved baseline TSV.

The TSV has source and warning columns; warnings omit the Lean location prefix.
This is a review aid, not an assertion that moved declarations or changed
suggestions represent identical diagnostics. Run after the project build.
"""
import collections
import csv
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


def main():
    if len(sys.argv) != 2:
        print('usage: compare_warnings.py BASELINE.tsv', file=sys.stderr)
        return 2
    with open(sys.argv[1]) as f:
        baseline = list(csv.DictReader(f, delimiter='\t'))
    current, missing = [], []
    for source in sorted((ROOT / 'MTC').rglob('*.lean')):
        rel = source.relative_to(ROOT)
        trace = ROOT / '.lake/build/lib/lean' / rel.with_suffix('.trace')
        if not trace.exists():
            missing.append(str(rel))
            continue
        for entry in json.loads(trace.read_text()).get('log', []):
            if entry.get('level') == 'warning':
                message = re.sub(r'^[^\n]*\.lean:\d+:\d+:\s*', '', entry['message'])
                current.append({'source': str(rel), 'warning': message})
    old = collections.Counter(d['warning'] for d in baseline)
    new = collections.Counter(d['warning'] for d in current)
    print(f'Baseline warnings: {sum(old.values())}; current warnings: {sum(new.values())}; missing traces: {len(missing)}')
    for label, counter in [('New or changed diagnostics', new - old), ('Removed or changed diagnostics', old - new)]:
        print(f'\n{label}: {sum(counter.values())}')
        for message, count in sorted(counter.items()):
            paths = sorted({d['source'] for d in (current if label.startswith('New') else baseline)
                            if d['warning'] == message})
            print(f'\n{count} x {", ".join(paths)}\n{message}')
    if missing:
        print('\nMissing traces:\n' + '\n'.join(missing), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
