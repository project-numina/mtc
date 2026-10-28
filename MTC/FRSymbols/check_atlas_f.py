#!/usr/bin/env python3
"""Check a bounded prefix of Atlas F blocks in the supplied basis.

This exact Python diagnostic checks ordinary matrix unitarity only; a failed
check does not rule out a unitary category in a different gauge.
"""
import argparse
from pathlib import Path
import struct

from import_atlas_block import read_block, read_exact
from check_atlas_r import CyclotomicArithmetic


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("payload", type=Path, help="unpacked F-symbol .aasym payload")
    parser.add_argument("--limit", type=int, default=5, help="maximum blocks to inspect")
    args = parser.parse_args()
    if args.limit <= 0:
        parser.error("--limit must be positive")
    with args.payload.open("rb") as stream:
        if read_exact(stream, 8) != b"ANYSYM01":
            raise ValueError("not an ANYSYM01 payload")
        version, kind, rank, degree, order, reserved, count = struct.unpack(
            "<BBBBHHI", read_exact(stream, 12)
        )
        if version != 1 or kind != 1 or reserved != 0 or not 0 < degree <= 32 or order == 0:
            raise ValueError("unsupported F-symbol payload")
        field = CyclotomicArithmetic(order, degree)
        for _ in range(min(count, args.limit)):
            labels, rows, cols, entries = read_block(stream, degree, kind)
            if any(label >= rank for label in labels) or rows == 0 or cols == 0:
                raise ValueError(f"invalid F block {labels}")
            result = field.unitary(rows, cols, entries)
            row_norm = field.zero
            for value in entries[:cols]:
                row_norm = field.add(row_norm, field.multiply(value, field.conjugate(value)))
            print(f"F{labels}, {rows}x{cols}: unitary={result}, first row norm²=1: {row_norm == field.one}")
    print("These are exact checks of the supplied basis, not a test of categorical unitarity or coherence.")


if __name__ == "__main__":
    main()
