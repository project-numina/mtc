#!/usr/bin/env python3
"""Generate one Lean matrix from a local Anyon Atlas ANYSYM01 symbol payload.

Only data supplied locally by the user are read. The output is a Lean file;
keep generated files under ignored data/ unless redistribution is authorized.
"""

import argparse
from pathlib import Path
import struct


def read_exact(stream, count):
    data = stream.read(count)
    if len(data) != count:
        raise ValueError("truncated symbol payload")
    return data


def uvarint(stream):
    value = 0
    shift = 0
    while True:
        byte = read_exact(stream, 1)[0]
        value |= (byte & 127) << shift
        if byte < 128:
            return value
        shift += 7
        if shift > 1000000:
            raise ValueError("unreasonably large varint")


def svarint(stream):
    value = uvarint(stream)
    return value // 2 if value % 2 == 0 else -(value // 2) - 1


def read_block(stream, degree, kind):
    raw_labels = tuple(read_exact(stream, 4))
    if kind == 2 and raw_labels[3] != 255:
        raise ValueError("invalid R block padding")
    labels = raw_labels if kind == 1 else raw_labels[:3]
    rows, cols = struct.unpack("<HH", read_exact(stream, 4))
    masks = []
    for _ in range(rows * cols):
        code = read_exact(stream, 1)[0]
        if code == 0:
            mask = 0
        elif code == 1:
            mask = (1 << degree) - 1
        elif code == 2:
            mask = struct.unpack("<I", read_exact(stream, 4))[0]
        else:
            raise ValueError("unknown coefficient mask")
        if mask >> degree:
            raise ValueError("coefficient mask exceeds field degree")
        masks.append(mask)
    denominators = [uvarint(stream) if mask else 1 for mask in masks]
    if any(den == 0 for den in denominators):
        raise ValueError("zero coefficient denominator")
    values = []
    for mask, den in zip(masks, denominators):
        coefficients = [svarint(stream) if mask & (1 << i) else 0 for i in range(degree)]
        values.append((den, coefficients))
    return labels, rows, cols, values


def rational(num, den):
    return f"(({num} : ℚ) / {den})" if den != 1 else f"({num} : ℚ)"


def polynomial(entry):
    den, coefficients = entry
    terms = []
    for power, num in enumerate(coefficients):
        if num:
            coefficient = f"C {rational(num, den)}"
            terms.append(coefficient if power == 0 else f"({coefficient} * X ^ {power})")
    return " + ".join(terms) if terms else "0"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("payload", type=Path, help="unpacked .aasym payload")
    parser.add_argument("labels", nargs="+", type=int, help="F: a b c d; R: a b c")
    parser.add_argument("--output", required=True, type=Path, help="output Lean file")
    args = parser.parse_args()
    with args.payload.open("rb") as stream:
        if read_exact(stream, 8) != b"ANYSYM01":
            raise ValueError("not an ANYSYM01 symbol payload")
        version, kind, rank, degree, order, reserved, count = struct.unpack(
            "<BBBBHHI", read_exact(stream, 12)
        )
        if version != 1 or kind not in (1, 2) or reserved != 0 or not 0 < degree <= 32:
            raise ValueError("unsupported symbol payload header")
        if len(args.labels) != (4 if kind == 1 else 3) or any(x < 0 or x >= rank for x in args.labels):
            raise ValueError("incorrect labels for symbol kind and rank")
        wanted = tuple(args.labels)
        for _ in range(count):
            labels, rows, cols, values = read_block(stream, degree, kind)
            if labels == wanted:
                break
        else:
            raise ValueError("block not found; strict-unit F blocks may be omitted")
    if not rows or not cols:
        raise ValueError("empty blocks are not emitted")
    name = "F" if kind == 1 else "R"
    namespace = f"AtlasGenerated.{name}{rank}_" + "_".join(map(str, wanted))
    lines = ["module", "public import MTC.FRSymbols.Cyclotomic", "public import Mathlib.Tactic",
             "", "@[expose] public noncomputable section", "open Polynomial MTC.FRSymbols", "",
             f"namespace {namespace}", ""]
    for row in range(rows):
        for col in range(cols):
            entry = polynomial(values[row * cols + col])
            lines.append(f"def entry_{row}_{col} : ExactCyclotomic {order} :=")
            lines.append(f"  AdjoinRoot.mk (cyclotomic {order} ℚ) ({entry})")
    lines.append("")
    lines.append(f"/-- Atlas {name} block {wanted}; source basis order is unchanged. -/")
    lines.append(f"def block : Matrix (Fin {rows}) (Fin {cols}) (ExactCyclotomic {order}) :=")
    row_text = [", ".join(f"entry_{row}_{col}" for col in range(cols)) for row in range(rows)]
    lines.append("  !![" + ";\n    ".join(row_text) + "]")
    lines.extend(["", f"end {namespace}", ""])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines), encoding="utf-8")
    print(f"Generated {name} block {wanted}: {rows} x {cols} over Q(zeta_{order}) in {args.output}")


if __name__ == "__main__":
    main()
