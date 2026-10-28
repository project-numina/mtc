#!/usr/bin/env python3
"""Check individual Atlas R matrices exactly in a cyclotomic power basis.

This is a reproducible Python check, not a Lean proof or a coherence test.
The payload must first be downloaded and verified against the Atlas manifest.
Requires SymPy for the cyclotomic polynomial and otherwise uses Python integers.
"""
import argparse
from math import gcd
from pathlib import Path
import struct

from sympy import Poly, cyclotomic_poly, symbols
from import_atlas_block import read_block, read_exact


class CyclotomicArithmetic:
    def __init__(self, order, degree):
        x = symbols("x")
        phi = Poly(cyclotomic_poly(order, x), x)
        if phi.degree() != degree or phi.LC() != 1:
            raise ValueError("field order and degree do not match Φ_n")
        self.degree = degree
        self.modulus = tuple(int(phi.nth(i)) for i in range(degree + 1))
        self.zero = (1, (0,) * degree)
        self.one = (1, (1,) + (0,) * (degree - 1))
        self.conjugate_basis = []
        for i in range(degree):
            power = (-i) % order
            monomial = [0] * (power + 1)
            monomial[power] = 1
            self.conjugate_basis.append(self.reduce(monomial))

    def reduce(self, polynomial):
        terms = list(polynomial)
        if len(terms) < self.degree:
            terms.extend([0] * (self.degree - len(terms)))
        for i in range(len(terms) - 1, self.degree - 1, -1):
            lead = terms[i]
            if lead:
                for j in range(self.degree):
                    terms[i - self.degree + j] -= lead * self.modulus[j]
        return tuple(terms[:self.degree])

    def normalize(self, den, values):
        divisor = den
        for value in values:
            divisor = gcd(divisor, value)
        return den // divisor, tuple(value // divisor for value in values)

    def add(self, left, right):
        dl, vl = left
        dr, vr = right
        common = gcd(dl, dr)
        lscale, rscale = dr // common, dl // common
        return self.normalize(dl * lscale, [lscale * a + rscale * b for a, b in zip(vl, vr)])

    def multiply(self, left, right):
        dl, vl = left
        dr, vr = right
        result = [0] * (2 * self.degree - 1)
        for i, a in enumerate(vl):
            if a:
                for j, b in enumerate(vr):
                    if b:
                        result[i + j] += a * b
        return self.normalize(dl * dr, self.reduce(result))

    def conjugate(self, value):
        den, coeffs = value
        result = [0] * self.degree
        for coefficient, basis in zip(coeffs, self.conjugate_basis):
            if coefficient:
                for j, component in enumerate(basis):
                    result[j] += coefficient * component
        return self.normalize(den, result)

    def unitary(self, rows, cols, entries):
        if rows == 0 or rows != cols:
            return False
        conjugates = [self.conjugate(entry) for entry in entries]
        for i in range(rows):
            for j in range(rows):
                value = self.zero
                for k in range(cols):
                    value = self.add(value, self.multiply(entries[i * cols + k], conjugates[j * cols + k]))
                if value != (self.one if i == j else self.zero):
                    return False
        return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("payload", type=Path, help="unpacked R-symbol .aasym payload")
    args = parser.parse_args()
    with args.payload.open("rb") as stream:
        if read_exact(stream, 8) != b"ANYSYM01":
            raise ValueError("not an ANYSYM01 payload")
        version, kind, rank, degree, order, reserved, count = struct.unpack(
            "<BBBBHHI", read_exact(stream, 12)
        )
        if version != 1 or kind != 2 or reserved != 0 or not 0 < degree <= 32 or order == 0:
            raise ValueError("unsupported R-symbol payload")
        field = CyclotomicArithmetic(order, degree)
        seen = set()
        for index in range(count):
            labels, rows, cols, entries = read_block(stream, degree, kind)
            if any(label >= rank for label in labels) or labels in seen:
                raise ValueError(f"invalid or duplicate block {labels}")
            seen.add(labels)
            if not field.unitary(rows, cols, entries):
                raise ValueError(f"R block {labels} is not unitary")
        if stream.read(1):
            raise ValueError("unexpected data after final block")
    print(f"Exactly checked {count} R blocks over Q(zeta_{order}); all are unitary.")
    print("This Python calculation does not verify completeness, F symbols, hexagons, or a category.")


if __name__ == "__main__":
    main()
