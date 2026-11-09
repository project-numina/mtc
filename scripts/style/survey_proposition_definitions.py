#!/usr/bin/env python3
"""Audit proof-valued definitions omitted by a theorem-only source census."""
import csv
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
STYLE = ROOT / 'scripts/style'
OUT = ROOT / 'docs/style'
GENERATED = re.compile(r'(?:\._f(?:_\d+)?$|\.match_\d|\._proof_\d|\._simp_\d|\.eq_\d|\.eq_def|\._aux_|\.brecOn|\.recOn|\.casesOn|\._flat_ctor)')


def report(raw):
    with raw.open() as f:
        rows = list(csv.DictReader(f, delimiter='\t'))
    rows.sort(key=lambda row: (row['module'], row['name']))
    with (OUT / 'proposition-definitions.tsv').open('w') as f:
        w = csv.DictWriter(f, ['classification', 'module', 'name'], delimiter='\t', lineterminator='\n')
        w.writeheader()
        for row in rows:
            w.writerow({'classification': 'generated-name pattern' if GENERATED.search(row['name']) else 'review', **row})
    print(f"Proof-valued definitions: {len(rows)}; require review: {sum(not GENERATED.search(r['name']) for r in rows)}")


def main():
    imports = '\n'.join(re.findall(r'^import all .+$', (ROOT / 'MTC/PropertyF/Audit/TargetAudit.lean').read_text(), re.M))
    source = 'module\npublic meta import Lean\n' + imports + '\n' + (STYLE / 'PropositionDefinitions.lean').read_text()
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=ROOT / 'scratch', delete=False) as f:
        f.write(source)
        filename = f.name
    try:
        subprocess.run(['taskset', '-c', os.environ.get('PROPERTYF_AUDIT_CORES', '0-3'),
                        'lake', 'env', 'lean', filename], cwd=ROOT, check=True)
    finally:
        Path(filename).unlink()
    report(STYLE / '.proposition-definitions.tsv')


if __name__ == '__main__':
    main()
