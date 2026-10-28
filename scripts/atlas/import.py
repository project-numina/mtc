#!/usr/bin/env python3
"""Convert verified Atlas source shards to an exact raw Lean encoding and JSON index."""
import argparse
import gzip
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
import re

FAMILIES = ('identifiers-exact', 'modular-exact', 'structure', 'fusion')
TERM = re.compile(r'(?:(\d+(?:/\d+)?)\*)?E\((\d+)/(\d+)\)|(\d+(?:/\d+)?)')


def parse_expression(value):
    """Parse only the source grammar, never evaluate arbitrary input."""
    text = value.replace(' ', '')
    pos = 0
    terms = []
    while pos < len(text):
        sign = 1
        if text[pos] in '+-':
            sign = -1 if text[pos] == '-' else 1
            pos += 1
        elif pos:
            raise ValueError(f'missing sign: {value!r}')
        match = TERM.match(text, pos)
        if not match:
            raise ValueError(f'unsupported cyclotomic expression: {value!r}')
        coef, num, den, constant = match.groups()
        coeff = sign * Fraction(constant or coef or '1')
        phase = Fraction(int(num), int(den)) if num is not None else Fraction(0)
        terms.append((coeff.numerator, coeff.denominator, phase.numerator, phase.denominator))
        pos = match.end()
    if not terms:
        raise ValueError('empty cyclotomic expression')
    return terms


def load_shard(root, descriptor, family, kind, rank, chunk):
    raw = (root / descriptor['file']).read_bytes()
    if hashlib.sha256(raw).hexdigest() != descriptor['sha256']:
        raise ValueError('hash mismatch: ' + descriptor['file'])
    data = json.loads(gzip.decompress(raw))
    if (data['schemaVersion'], data['family'], data['kind'], data['rank'], data['chunk']) != (1, family, kind, rank, chunk):
        raise ValueError('shard header mismatch: ' + descriptor['file'])
    return data['records']


def records(root):
    manifest = json.loads((root / 'manifest.json').read_text())
    if manifest['schemaVersion'] != 1:
        raise ValueError('unsupported manifest schema')
    seen = set()
    for kind, group in manifest['kinds'].items():
        for rank in group['ranks']:
            for chunk in rank['chunks']:
                tables = {}
                for family in FAMILIES:
                    rows = load_shard(root, chunk['families'][family], family, kind, rank['rank'], chunk['index'])
                    ids = [row['id'] for row in rows]
                    if ids != chunk['ids'] or len(ids) != len(set(ids)):
                        raise ValueError(f'{kind} {rank["rank"]} {chunk["index"]}: missing, duplicate or reordered IDs in {family}')
                    tables[family] = rows
                for entries in zip(*(tables[f] for f in FAMILIES)):
                    identifier, modular, structure, fusion = entries
                    rid = identifier['id']
                    if rid in seen:
                        raise ValueError(f'duplicate ID {rid}')
                    seen.add(rid)
                    yield kind, rank['rank'], chunk['index'], identifier, modular, structure, fusion
    if len(seen) != manifest['counts']['total']:
        raise ValueError(f'expected {manifest["counts"]["total"]} records, found {len(seen)}')


def lean_string(value):
    return json.dumps(value, ensure_ascii=False)


def lean_expr(value):
    def integer(n):
        return f'({n})' if n < 0 else str(n)
    return '[' + ', '.join('⟨' + ', '.join(map(integer, term)) + '⟩' for term in parse_expression(value)) + ']'


def lean_record(kind, rank, modular):
    matrix = '[' + ',\n    '.join('[' + ', '.join(map(lean_expr, row)) + ']' for row in modular['S']) + ']'
    twists = '[' + ', '.join(map(lean_expr, modular['T'])) + ']'
    return ('  { id := ' + lean_string(modular['id']) + ', kind := ' + lean_string(kind) +
            f', rank := {rank},\n    s := {matrix},\n    t := {twists} }}')


def index_row(kind, rank, identifiers, modular, structure):
    p = structure['propertiesRealizations']
    orders = (int(m.group(1)) for expr in [x for row in modular['S'] for x in row] + modular['T'] for m in re.finditer(r'E\(\d+/(\d+)\)', expr))
    field_order = math.lcm(1, *orders)
    return {'id': identifiers['id'], 'kind': kind, 'rank': rank,
            'globalDimensionSquared': identifiers['globalDimensionSquared'],
            'centralCharge': identifiers.get('centralCharge'),
            'quantumDimensions': identifiers['quantumDimensions'],
            'twistOrder': p.get('frobeniusSchurExponent'),
            'cyclotomicFieldOrderUpperBound': field_order,
            'weaklyIntegral': p.get('weaklyIntegral'),
            'positiveDimensions': p.get('positiveDimensions'),
            'realizations': p.get('realizations', []),
            'knownProductRealization': p.get('knownProductRealization'),
            'whitelistedRealizations': p.get('whitelistedRealizations', []),
            'chernSimonsEligibility': p.get('chernSimonsEligibility')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path('data/atlas'))
    parser.add_argument('--output', type=Path, default=Path('data/generated'))
    parser.add_argument('--max-module-bytes', type=int, default=262144, help='target size; an individual record is never split')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    if args.max_module_bytes <= 0:
        parser.error('--max-module-bytes must be positive')
    if any(args.output.glob('*.lean')) or (args.output / 'index.json').exists():
        parser.error('output directory already contains generated files; choose a new directory')
    index = []
    previous = None
    module_bytes = 0
    file = None
    try:
        for kind, rank, chunk, identifiers, modular, structure, fusion in records(args.source):
            key = kind, rank, chunk
            encoded = lean_record(kind, rank, modular)
            encoded_bytes = len(encoded.encode('utf-8'))
            if key != previous:
                part = 0
            elif module_bytes + encoded_bytes > args.max_module_bytes:
                part += 1
            else:
                part = part
            if key != previous or module_bytes + encoded_bytes > args.max_module_bytes:
                if file:
                    file.write('\n]\n\nend AnyonAtlas.Generated\n')
                    file.close()
                name = f'{kind}Rank{rank:02}Chunk{chunk:03}Part{part:03}'
                path = args.output / f'{name[0].upper() + name[1:]}.lean'
                file = path.open('w')
                file.write('module\npublic import AnyonAtlas.Raw\n\n/-! Generated from Atlas exact export. -/\n\n@[expose] public section\nnamespace AnyonAtlas.Generated\n\ndef ' + name + ' : List RawRecord := [\n')
                previous = key
                module_bytes = 0
                first = True
            if not first:
                file.write(',\n')
            file.write(encoded)
            module_bytes += encoded_bytes
            first = False
            index.append(index_row(kind, rank, identifiers, modular, structure))
        if file:
            file.write('\n]\n\nend AnyonAtlas.Generated\n')
    finally:
        if file:
            file.close()
    manifest = json.loads((args.source / 'manifest.json').read_text())
    (args.output / 'index.json').write_text(json.dumps({'sourceFingerprint': manifest['sourceFingerprint'], 'records': index}, indent=2) + '\n')
    print(f'Imported {len(index)} records in exact cyclotomic syntax.')


if __name__ == '__main__':
    main()
