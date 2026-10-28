#!/usr/bin/env python3
"""Reproduce a descriptive rank study from the public Anyon Atlas export.

The source files remain in the ignored scratch directory. Numerical values are
approximations supplied by the Atlas, not Lean proofs or classification bounds.
"""
import concurrent.futures
import gzip
import hashlib
import json
import math
from pathlib import Path
import subprocess

BASE = 'https://anyonatlas.org/export-v1/'
CACHE = Path('scratch/rank-atlas')


def fetch(path, digest=None):
    target = CACHE / path
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(['curl', '--fail', '--silent', '--show-error', '--location',
                                 BASE + path], check=True, capture_output=True)
        target.write_bytes(result.stdout)
    result = target.read_bytes()
    if digest and hashlib.sha256(result).hexdigest() != digest:
        raise ValueError(f'Checksum mismatch: {path}')
    return result


def load_chunk(chunk):
    family = chunk['families']['identifiers-numeric']
    raw = fetch(family['file'], family['sha256'])
    result = json.loads(gzip.decompress(raw))
    if len(result['records']) != chunk['count']:
        raise ValueError('Chunk count mismatch')
    return result['records']


def fit(xs, ys):
    lx = [math.log(x) for x in xs]
    ly = [math.log(y) for y in ys]
    def line(x):
        xm, ym = sum(x)/len(x), sum(ly)/len(ly)
        slope = sum((a-xm)*(b-ym) for a,b in zip(x,ly))/sum((a-xm)**2 for a in x)
        intercept = ym-slope*xm
        residual = sum((b-intercept-slope*a)**2 for a,b in zip(x,ly))
        total = sum((b-ym)**2 for b in ly)
        return intercept, slope, 1-residual/total
    return {'exponential': line(xs), 'power': line(lx)}


def main():
    manifest = json.loads(fetch('manifest.json'))
    ranks = manifest['kinds']['bosonic']['ranks']
    chunks = [chunk for rank in ranks for chunk in rank['chunks']]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        records = [r for group in pool.map(load_chunk, chunks) for r in group]
    assert len(records) == manifest['counts']['bosonic']
    rows = []
    for rank in ranks:
        entries = [r for r in records if r['rank'] == rank['rank']]
        assert len(entries) == rank['count']
        # In these numerical exports all-positive unit rows select the
        # pseudo-unitary pivotal structures, with a conservative tolerance.
        positives = [r for r in entries if all(abs(z[1]) < 1e-8 and z[0] > 1e-8
                     for z in r['quantumDimensions'])]
        top = max(positives, key=lambda r: r['globalDimensionSquared'])
        rows.append({'rank': rank['rank'], 'count': len(entries),
                     'positive_count': len(positives),
                     'max_global_dimension': top['globalDimensionSquared'],
                     'max_total_quantum_dimension': math.sqrt(top['globalDimensionSquared']),
                     'id': top['id']})
    print(json.dumps({'sourceFingerprint': manifest['sourceFingerprint'], 'rows': rows,
        'fits': {'counts': fit([r['rank'] for r in rows], [r['count'] for r in rows]),
                 'maximum_total_quantum_dimension': fit([r['rank'] for r in rows],
                     [r['max_total_quantum_dimension'] for r in rows])}}, indent=2))


if __name__ == '__main__':
    main()
