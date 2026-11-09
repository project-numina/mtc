#!/usr/bin/env python3
"""Check baseline source invariants for the six pivotal targets and generated category.

Exact source equality is deliberately stronger than equivalence. These hashes are
not an independent proof of manuscript faithfulness; that requires review.
"""
import hashlib
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
FILES = {
    'MTC/PropertyF/Statement.lean': 'c44c239051e515ec4274322571253add98f05e20266c1e7e5872afa9844ed9cf',
    'MTC/PropertyF/Theorem.lean': '2018f0da063b18c79993828b798d02a1bcc8f4ed83583b980bbdecfcf0bdfe11',
    'MTC/PropertyF/Pivotal/Statement.lean': 'adcf7a475434f5afce639c469c1f8d2e4ac182ceb71f96c16d06fb879faeeceb',
}
# Match whole declarations, including their values. Context and instances are
# still subject to review; these hashes alone do not pin elaborated semantics.
GENERATED = {
    'generatedProperty': 'f335b9846969c080436c05c030484365fcbcf5ae15436b67a0f4f7ccd5fe5922',
    'GeneratedCategory': '149f2d648de90490550bedba0dd95a2b8be4ccd7fe04d5e3f0150b70f6fd18cd',
    'generatedPieces': '41d745df1f4789f0a0171575867a8c5e67f9a63f61a667fac7269dc9ffec8587',
    'generatedPiecesDecomposition': 'f0d6d73a308b155408ee76ef9f4525731e31b25073b79ef512f6ee859c7725f1',
    'generatedLabels': 'aefab832aca96276893d089e5ca5c0401d3319910fe0234feffaee3601646007',
    'GeneratedSimpleIndex': 'b4216edd13ae54be2e60c7626fc36b4da3be465713b3978d4f5fafdf934626f8',
    'generatedSimple': '0245b3ec3f717b2517bf60192c8136b100f77feae3f7233c1241e17d2be5d4f9',
    'bundledGenerated': 'f3f5d88f9d9a9623e7bf4985bb2a7fec8d8456d41cf0234dc1d2fa21d1cebafb',
    'generatedObject': 'e2ec9cff1a741303631ad88c8febc81a80872be83fe0eac612600e58d3aebe44',
    'ObjectwiseStatement': '813a5273b31fa6026de1460cb6d3a41da9aa1fe5f06c246fe5163e48c5f0d7fe',
}


def declaration(text, name):
    start = re.search(r'(?m)^(?:def|abbrev) ' + re.escape(name) + r'\b', text)
    if not start:
        raise ValueError(f'missing generated-category declaration {name}')
    end = re.search(r'(?m)^(?:/--|/-!|(?:def|abbrev|theorem|instance|set_option|end)\b)', text[start.end():])
    return text[start.start():start.end() + end.start() if end else len(text)].strip().encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    errors = []
    for path, expected in FILES.items():
        if digest((ROOT / path).read_bytes()) != expected:
            errors.append(f'{path} differs from fb6ec518')
    text = (ROOT / 'MTC/PropertyF/Pivotal/GeneratedCategory.lean').read_text()
    for name, expected in GENERATED.items():
        if digest(declaration(text, name)) != expected:
            errors.append(f'generated-category declaration {name} differs from fb6ec518')
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print('Frozen files, pivotal target source and selected generated-category definitions match fb6ec518.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
