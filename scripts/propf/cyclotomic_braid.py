#!/usr/bin/env python3
"""Search exact cyclotomic braid matrices for a projective-infinite witness.

Each entry is a list of rational coefficients in ascending powers of a fixed
primitive root zeta_n. Example: ["1/2", "-1"] means 1/2 - zeta_n.
"""

import argparse
from collections import deque
import json
import sys

import sympy as sp
from sympy.polys.domains import QQ
from sympy.polys.matrices import DomainMatrix

from braid_infinite import RATIONAL


def parse_rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, str)) or not RATIONAL.fullmatch(str(value)):
        raise ValueError(f"invalid rational coefficient: {value!r}")
    return QQ.convert(sp.Rational(value))


def read_generators(path):
    with open(path, encoding="utf-8") as stream:
        data = json.load(stream)
    order = data["order"]
    if isinstance(order, bool) or not isinstance(order, int) or not 2 <= order <= 1000:
        raise ValueError("order must be an integer between 2 and 1000")
    field = QQ.cyclotomic_field(order)
    raw = data["generators"]
    if not isinstance(raw, list) or not raw:
        raise ValueError("generators must be a nonempty list")
    matrices = []
    for rows in raw:
        if not isinstance(rows, list) or not rows or any(
            not isinstance(row, list) or len(row) != len(rows) for row in rows
        ):
            raise ValueError("each generator must be a nonempty square matrix")
        parsed = []
        for row in rows:
            entries = []
            for coeffs in row:
                if not isinstance(coeffs, list) or not coeffs:
                    raise ValueError("each entry must be a nonempty coefficient list")
                entry = field.zero
                for coeff in reversed(coeffs):
                    entry = entry * field.unit + field.convert(parse_rational(coeff))
                entries.append(entry)
            parsed.append(entries)
        matrices.append(DomainMatrix(parsed, (len(rows), len(rows)), field))
    if any(m.shape != matrices[0].shape for m in matrices):
        raise ValueError("all generators must have the same dimension")
    for i, a in enumerate(matrices):
        if a.det() == field.zero:
            raise ValueError(f"generator {i + 1} is singular")
        for j, b in enumerate(matrices[i + 1 :], i + 1):
            if j == i + 1 and a * b * a != b * a * b:
                raise ValueError(f"generators {i + 1}, {j + 1} violate the braid relation")
            if j > i + 1 and a * b != b * a:
                raise ValueError(f"generators {i + 1}, {j + 1} do not commute")
    return order, matrices


def element_polynomial(element, z):
    return sum(sp.Rational(c) * z**i for i, c in enumerate(reversed(element.to_list())))


def noncyclotomic_ratio(matrix, order):
    x, y, z = sp.symbols("x y z")
    degree = matrix.shape[0]
    coeffs = matrix.charpoly()
    p = sum(element_polynomial(c, z) * y**(degree-i) for i, c in enumerate(coeffs))
    ratios = sp.resultant(p, sp.expand(y**degree * p.subs(y, x*y)), y)
    norm = sp.resultant(sp.cyclotomic_poly(order, z), ratios, z)
    polynomial = sp.Poly(norm, x, domain=sp.QQ)
    for factor, _ in sp.factor_list(polynomial)[1]:
        if not factor.monic().is_cyclotomic:
            return {"characteristic_polynomial": str(p), "ratio_norm": str(polynomial.monic().as_expr()),
                    "noncyclotomic_factor": str(factor.monic().as_expr())}
    return None


def key(matrix):
    return tuple(tuple(tuple(value.to_list()) for value in row) for row in matrix.to_list())


def search(order, generators, max_length, max_nodes):
    field = generators[0].domain
    dimension = generators[0].shape[0]
    identity = DomainMatrix.eye((dimension, dimension), field).to_dense()
    alphabet = [(i + 1, g) for i, g in enumerate(generators)]
    alphabet += [(-(i + 1), g.inv()) for i, g in enumerate(generators)]
    seen = {key(identity)}
    queue = deque([(identity, ())])
    checked = 0
    while queue:
        matrix, word = queue.popleft()
        checked += 1
        if word:
            witness = noncyclotomic_ratio(matrix, order)
            if witness:
                return {"result": "infinite_projective_image", "word": word,
                        "checked_matrices": checked, **witness}
        if len(word) == max_length:
            continue
        for label, generator in alphabet:
            product = matrix * generator
            product_key = key(product)
            if product_key in seen:
                continue
            if len(seen) >= max_nodes:
                return {"result": "inconclusive_node_limit", "checked_matrices": checked}
            seen.add(product_key)
            queue.append((product, word + (label,)))
    return {"result": "inconclusive", "checked_matrices": checked}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--max-length", type=int, default=3)
    parser.add_argument("--max-nodes", type=int, default=100)
    args = parser.parse_args()
    if args.max_length < 1 or args.max_nodes < 2:
        parser.error("max-length must be positive and max-nodes at least 2")
    try:
        order, generators = read_generators(args.input)
        result = search(order, generators, args.max_length, args.max_nodes)
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError, json.JSONDecodeError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
