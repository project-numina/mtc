#!/usr/bin/env python3
"""Check an exact F-symbol table by producing and kernel-checking a Lean proof."""

import argparse
import hashlib
import itertools
import json
import os
from fractions import Fraction
from functools import lru_cache
from math import isqrt
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
MODULE = "MTC.FRSymbols.PentagonTable"


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"duplicate JSON key {key!r}")
        obj[key] = value
    return obj


def fields(obj, expected, where):
    if not isinstance(obj, dict) or set(obj) != set(expected.split()):
        raise ValueError(f"{where} must have exactly the fields {expected}")


def array(value, where, length=None):
    if not isinstance(value, list) or (length is not None and len(value) != length):
        size = "" if length is None else f" of length {length}"
        raise ValueError(f"{where} must be an array{size}")
    return value


def nat(value, where, upper=None):
    if type(value) is not int or value < 0 or (upper is not None and value >= upper):
        raise ValueError(f"invalid natural number {value!r} at {where}")
    return value


def totient(order):
    result = remaining = order
    factor = 2
    while factor * factor <= remaining:
        if remaining % factor == 0:
            result -= result // factor
            while remaining % factor == 0:
                remaining //= factor
        factor += 1 if factor == 2 else 2
    if remaining > 1:
        result -= result // remaining
    return result


@lru_cache(maxsize=None)
def cyclotomic(order):
    """Recover Φ_n from X^n - 1 by monic division by Φ_d for every proper divisor."""
    p = [-1] + [0] * (order - 1) + [1]
    divisors = set()
    for d in range(1, isqrt(order) + 1):
        if order % d == 0:
            divisors.update((d, order // d))
    for d in sorted(divisors - {order}):
        divisor = cyclotomic(d)
        quotient = [0] * (len(p) - len(divisor) + 1)
        for i in reversed(range(len(quotient))):
            coefficient = p[i + len(divisor) - 1]
            quotient[i] = coefficient
            if coefficient:
                for j, value in enumerate(divisor):
                    p[i + j] -= coefficient * value
        if any(p):
            raise ValueError("nonzero remainder computing cyclotomic polynomial")
        p = quotient
    return tuple(p)


def scalar(raw, degree, where):
    coordinates = array(raw, where)
    if len(coordinates) > degree:
        raise ValueError(f"{where} exceeds the power-basis degree {degree}")
    result = []
    for x in coordinates:
        if type(x) is int:
            result.append(Fraction(x))
        elif isinstance(x, str) and re.fullmatch(r"-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?", x):
            result.append(Fraction(x))
        else:
            raise ValueError(f"invalid rational coordinate {x!r} at {where}")
    while result and not result[-1]:
        result.pop()
    return tuple(result)


def read_table(payload):
    doc = json.loads(payload, object_pairs_hook=unique_object)
    fields(doc, "version order unit dual fusion strict_unit blocks", "document")
    if nat(doc["version"], "version") != 1:
        raise ValueError("unsupported schema version")
    order = nat(doc["order"], "order")
    if not order:
        raise ValueError("order must be positive")
    degree = totient(order)
    dual = array(doc["dual"], "dual")
    rank = len(dual)
    unit = nat(doc["unit"], "unit", rank)
    for i, j in enumerate(dual):
        nat(j, f"dual[{i}]", rank)
    if any(dual[j] != i for i, j in enumerate(dual)):
        raise ValueError("dual must be an involution")
    strict = doc["strict_unit"]
    if type(strict) is not bool:
        raise ValueError("strict_unit must be a boolean")

    fusion = array(doc["fusion"], "fusion", rank)
    for a, plane in enumerate(fusion):
        for b, row in enumerate(array(plane, f"fusion[{a}]", rank)):
            for c, n in enumerate(array(row, f"fusion[{a}][{b}]", rank)):
                nat(n, f"fusion[{a}][{b}][{c}]")
    labels = range(rank)
    for a, b in itertools.product(labels, repeat=2):
        if fusion[unit][a][b] != int(a == b) or fusion[a][unit][b] != int(a == b):
            raise ValueError(f"fusion unit law fails at labels {(a, b)}")
        if fusion[a][b][unit] != int(dual[a] == b):
            raise ValueError(f"fusion duality law fails at labels {(a, b)}")

    provided = {}
    for i, block in enumerate(array(doc["blocks"], "blocks")):
        fields(block, "labels rows", f"blocks[{i}]")
        key = tuple(nat(x, f"blocks[{i}].labels", rank)
                    for x in array(block["labels"], f"blocks[{i}].labels", 4))
        if key in provided:
            raise ValueError(f"duplicate F block {key}")
        provided[key] = block["rows"]

    blocks = []
    for key in itertools.product(labels, repeat=4):
        a, b, c, d = key
        rows = sum(fusion[a][b][x] * fusion[x][c][d] for x in labels)
        cols = sum(fusion[b][c][x] * fusion[a][x][d] for x in labels)
        if rows != cols:
            raise ValueError(f"nonassociative fusion at {key}: {rows} left and {cols} right channels")
        identity = strict and unit in (a, b, c)
        entries = []
        if key in provided:
            matrix = array(provided[key], f"F{key}", rows)
            for i, raw_row in enumerate(matrix):
                row = array(raw_row, f"F{key} row {i}", cols)
                for j, x in enumerate(row):
                    coefficient = scalar(x, degree, f"F{key}[{i},{j}]")
                    if identity and coefficient != ((1,) if i == j else ()):
                        raise ValueError(f"strict-unit block F{key} differs from identity at [{i},{j}]")
                    entries.append(coefficient)
        elif identity:
            entries = [(Fraction(1),) if i == j else () for i in range(rows) for j in range(cols)]
        elif rows:
            raise ValueError(f"missing F block {key} ({rows} × {cols})")
        blocks.append(entries)
    return order, unit, dual, fusion, blocks


def lean_array(items):
    return "#[" + ", ".join(items) + "]"


def lean_scalar(coefficients):
    def rational(x):
        if x.denominator == 1:
            return str(x.numerator)
        return f"({x.numerator} / {x.denominator})"
    return "[" + ", ".join(rational(x) for x in coefficients) + "]"


def table_source(payload):
    order, unit, dual, fusion, blocks = read_table(payload)
    digest = hashlib.sha256(payload).hexdigest()
    namespace = f"SubmittedPentagon.H_{digest}"
    flat = (str(n) for plane in fusion for row in plane for n in row)
    table_blocks = ",\n    ".join(lean_array(lean_scalar(x) for x in block) for block in blocks)
    header = f"""import {MODULE}

-- Source JSON SHA-256: {digest}
open MTC.FRSymbols
namespace {namespace}

def table : PentagonTable {len(dual)} where
  order := {order}
  unit := {unit}
  dual := {lean_array(map(str, dual))}
  fusion := {lean_array(flat)}
  blocks := #[
    {table_blocks}]
"""
    return header, lean_scalar(cyclotomic(order)[:-1]), namespace


def proof_source(payload):
    header, monic_tail, namespace = table_source(payload)
    return header + f"""
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem all_pentagons : table.Pentagon := by
  apply table.pentagon_of_check (monicTail := {monic_tail})
  · constructor <;> decide +kernel
  · decide +kernel
  · decide +kernel

end {namespace}
"""


def diagnostic_source(payload):
    """Replay individual checkEntry calls after an unsuccessful kernel proof."""
    header, monic_tail, namespace = table_source(payload)
    return header + f"""
#eval match table.firstFailure {monic_tail} with
  | some indices => IO.println s!"Failing pentagon (a,b,c,d,u,e,f,g,h,α,β,γ,δ,ζ,η) = {{indices}}"
  | none => IO.println "All pentagon entries passed the diagnostic run. The proof did not complete."

end {namespace}
"""


def verify(input_path, proof_path):
    payload = input_path.read_bytes()
    source = proof_source(payload)
    if proof_path and (proof_path.suffix != ".lean" or proof_path.resolve() == input_path.resolve()):
        raise ValueError("--proof must name a separate .lean file")
    subprocess.run(["lake", "build", MODULE], cwd=ROOT, check=True)
    # Rename only after the kernel has accepted this exact file.
    parent = proof_path.absolute().parent if proof_path else None
    with tempfile.TemporaryDirectory(dir=parent) as directory:
        proof = Path(directory) / "SubmittedPentagon.lean"
        proof.write_text(source, encoding="utf-8")
        checked = subprocess.run(["lake", "env", "lean", str(proof)], cwd=ROOT)
        if checked.returncode:
            diagnostic = Path(directory) / "PentagonDiagnostic.lean"
            diagnostic.write_text(diagnostic_source(payload), encoding="utf-8")
            subprocess.run(["lake", "env", "lean", str(diagnostic)], cwd=ROOT)
            checked.check_returncode()
        if proof_path:
            os.replace(proof, proof_path)
    return hashlib.sha256(payload).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="version 1 F-table JSON")
    parser.add_argument("--proof", type=Path, help="save the checked, replayable .lean proof")
    args = parser.parse_args()
    try:
        digest = verify(args.input, args.proof)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        return 1
    print(f"Verified all pentagons for input SHA-256 {digest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
