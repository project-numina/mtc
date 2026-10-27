#!/usr/bin/env python3
"""Extract complete warning blocks from a successful Lake build/replay."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[2]
lines = (root/'scripts/style/.build.log').read_text().splitlines()
blocks=[]; block=None
for line in lines:
    if re.match(r'^warning:', line):
        if block: blocks.append(block)
        block=[line]
    elif block is not None:
        if re.match(r'^(?:✔|ℹ|⚠|✖|error:|info:|Build completed)', line):
            blocks.append(block); block=None
        else: block.append(line)
if block: blocks.append(block)
blocks.sort(key=lambda block: '\n'.join(block))
out = root/'STYLE_LINT_BUILD.txt'
out.write_text('Mathlib default linter warnings from lake build PropertyF (including replayed modules).\n'
               f'Warning blocks: {len(blocks)}\n\n'+'\n\n'.join('\n'.join(b).rstrip() for b in blocks)+'\n')
print(f'Wrote {len(blocks)} default warning blocks to {out.name}')
