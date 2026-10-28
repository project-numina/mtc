#!/usr/bin/env python3
"""Validate source schema and numerically check necessary matrix identities.

This is a floating-point diagnostic, not an exact proof or a categorification test.
"""
import argparse
from functools import lru_cache
import json
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
os.environ.setdefault('OMP_NUM_THREADS', '1')
import numpy as np
import importlib.util
from pathlib import Path
import sys

spec = importlib.util.spec_from_file_location('atlas_import', Path(__file__).with_name('import.py'))
atlas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(atlas)
spec2 = importlib.util.spec_from_file_location('atlas_query', Path(__file__).with_name('query.py'))
query = importlib.util.module_from_spec(spec2)
spec2.loader.exec_module(query)
numeric = lru_cache(maxsize=30000)(query.numeric)


def close(a, b, tol):
    return np.allclose(a, b, rtol=tol, atol=tol)


def check(kind, rank, ids, modular, structure, fusion, tol):
    errors = []
    if ids.get('rank') != rank or ids.get('kind') != kind or fusion.get('rank') != rank:
        errors.append('record kind or rank')
    s0, t0 = modular['S'], modular['T']
    if len(s0) != rank or any(len(row) != rank for row in s0) or len(t0) != rank:
        return ['matrix shape']
    if modular.get('tEncoding') != 'diagonal':
        return ['unexpected T encoding']
    S = np.array([[numeric(x) for x in row] for row in s0])
    T = np.array([numeric(x) for x in t0])
    dims = np.array([numeric(x) for x in ids['quantumDimensions']])
    if not np.isfinite(S).all() or not np.isfinite(T).all() or not np.isfinite(dims).all():
        return errors + ['non-finite numerical approximation']
    if dims.shape != (rank,):
        return ['dimension vector shape']
    if not close(S, S.T, tol): errors.append('S symmetry')
    if not close(S[0], dims, tol): errors.append('vacuum row')
    if not close(S[0, 0], 1, tol) or not close(T[0], 1, tol): errors.append('vacuum normalization')
    if not close(np.abs(T), np.ones(rank), tol): errors.append('unit modulus twists')
    order = structure['propertiesRealizations']['frobeniusSchurExponent']
    if not isinstance(order, int) or order <= 0 or not close(T ** order, np.ones(rank), tol * max(1, order)):
        errors.append('twist order')
    if ids['twists'] != t0:
        errors.append('identifier twists differ from T')
    if kind == 'bosonic':
        d2 = np.sum(dims * dims)
        S2 = S @ S
        if not close(S @ S.conj().T, d2 * np.eye(rank), tol): errors.append('scaled unitarity')
        if abs(d2) < tol:
            errors.append('zero dimension')
        else:
            C = S2 / d2
            dual = np.argmax(np.abs(C), axis=1)
            expected = np.eye(rank)[dual]
            if not close(C, expected, tol) or len(set(dual)) != rank or any(dual[dual[i]] != i for i in range(rank)) or dual[0] != 0:
                errors.append('S squared / charge conjugation')
            st = S * T[np.newaxis, :]
            gauss = np.sum(dims * dims * T)
            if not close(st @ st @ st, gauss * S2, tol): errors.append('modular relation')
    if fusion.get('encoding') != 'compact-sparse-commutative-v1' or not fusion.get('lifts'):
        errors.append('fusion encoding')
    for lift in fusion.get('lifts', []):
        offsets, terms = lift['offsets'], lift['terms']
        if len(offsets) != rank * (rank + 1) // 2 + 1 or offsets[0] != 0 or offsets[-1] != len(terms) or any(a > b or a % 2 for a, b in zip(offsets, offsets[1:])) or len(terms) % 2 or any(not isinstance(x, int) or x < 0 for x in terms):
            errors.append('fusion sparse structure')
            break
        if any(terms[i] >= rank or terms[i + 1] == 0 for i in range(0, len(terms), 2)):
            errors.append('fusion sparse terms')
            break
        if kind == 'bosonic':
            tensor = np.zeros((rank, rank, rank), dtype=np.int64)
            idx = 0
            for i in range(rank):
                for j in range(i, rank):
                    for p in range(offsets[idx], offsets[idx + 1], 2):
                        c, coefficient = terms[p:p + 2]
                        tensor[i, j, c] += coefficient
                        if i != j:
                            tensor[j, i, c] += coefficient
                    idx += 1
            if np.any(np.abs(dims) < tol):
                errors.append('zero vacuum-row entry')
            else:
                lhs = S[:, None, :] * S[None, :, :] / dims[None, None, :]
                rhs = np.einsum('abc,cx->abx', tensor, S, optimize=True)
                if not close(lhs, rhs, tol): errors.append('fusion diagonalization')
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path('data/atlas'))
    parser.add_argument('--report', type=Path, default=Path('data/validation.json'))
    parser.add_argument('--tolerance', type=float, default=1e-6)
    args = parser.parse_args()
    if args.tolerance <= 0:
        parser.error('tolerance must be positive')
    counts = {'bosonic': 0, 'fermionic': 0}
    failures = []
    for kind, rank, _, ids, modular, structure, fusion in atlas.records(args.source):
        counts[kind] += 1
        try:
            errors = check(kind, rank, ids, modular, structure, fusion, args.tolerance)
        except (ValueError, KeyError, TypeError, OverflowError) as e:
            errors = [f'{type(e).__name__}: {e}']
        if errors:
            failures.append({'id': ids['id'], 'checks': errors})
        if sum(counts.values()) % 1000 == 0:
            print(f"Checked {sum(counts.values())} records; {len(failures)} flagged", flush=True)
    manifest = json.loads((args.source / 'manifest.json').read_text())
    report = {'sourceFingerprint': manifest['sourceFingerprint'], 'counts': counts, 'tolerance': args.tolerance,
              'method': 'floating-point necessary conditions; not a proof', 'failures': failures}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f"Checked {sum(counts.values())} records; {len(failures)} flagged. Report: {args.report}")
    return bool(failures)


if __name__ == '__main__':
    sys.exit(main())
