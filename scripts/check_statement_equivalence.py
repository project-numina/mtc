#!/usr/bin/env python3
"""Check the theorem statement sources against the pre-restructure snapshot.

Hashes cover Lean code after the specified import and namespace renames, ignoring
comments and whitespace. The baseline is commit 16b4d1e4; the complete old files
can be inspected with git show. Both files contain the project's entire definition
cone for TargetStatement; imported Mathlib is pinned separately by Lake.
"""
import hashlib
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
FROZEN = {
    'MTC/Braided/Definitions.lean': '69a4e4647ddb4ce40c87924982eb953226ef01bae00afe4f13c5bda0ff040150',
    'MTC/PropertyF/Statement.lean': '06a9b850d944ce94c4a00eae21fd0a3228672181202ae36c91e1beb0aba10f69',
}


def normalize(text):
    """Discard nested Lean comments, retaining strings and code tokens."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif pair == '/-':
            depth = 1
            out.append(' ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
            out.append(' ')
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise ValueError('unterminated comment or string')
    return re.sub(r'\s+', ' ', ''.join(out)).strip()


def main():
    for filename, expected in FROZEN.items():
        actual = hashlib.sha256(normalize((ROOT / filename).read_text(encoding='utf-8')).encode()).hexdigest()
        if actual != expected:
            print(f'{filename}: statement-cone source differs from the recorded baseline', file=sys.stderr)
            return 1
    print('Statement-cone sources match the recorded baseline after renaming.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
