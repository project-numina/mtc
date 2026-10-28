#!/usr/bin/env python3
"""Search rational braid matrices for a rigorous projective-infinite witness.

Input JSON: {"generators": [[["1", "0"], ["0", "-1"]], ...]}.
Entries must be integers or rational strings p/q. Matrices represent consecutive
Artin generators sigma_1,...,sigma_(n-1) in a common basis. This tool checks all
Artin relations and invertibility exactly, then searches bounded words.
"""

import argparse
from collections import deque
import json
import re
import sys

import sympy as sp

RATIONAL = re.compile(r"[+-]?\d+(?:/[+-]?\d+)?\Z")


def read_generators(path):
    with open(path, encoding="utf-8") as stream:
        data = json.load(stream)
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
            for value in row:
                if isinstance(value, bool) or not isinstance(value, (int, str)):
                    raise ValueError("entries must be integers or rational strings")
                if not RATIONAL.fullmatch(str(value)):
                    raise ValueError(f"invalid rational entry: {value!r}")
                entries.append(sp.Rational(value))
            parsed.append(entries)
        matrices.append(sp.ImmutableMatrix(parsed))
    if any(m.shape != matrices[0].shape for m in matrices):
        raise ValueError("all generators must have the same dimension")
    for i, a in enumerate(matrices):
        if a.det() == 0:
            raise ValueError(f"generator {i + 1} is singular")
        for j, b in enumerate(matrices[i + 1 :], i + 1):
            if j == i + 1 and a * b * a != b * a * b:
                raise ValueError(f"generators {i + 1}, {j + 1} violate the braid relation")
            if j > i + 1 and a * b != b * a:
                raise ValueError(f"generators {i + 1}, {j + 1} do not commute")
    return matrices


def noncyclotomic_ratio(matrix):
    """Return a factor witnessing an eigenvalue ratio that is not a root of unity.

    For P(t)=det(tI-M), Res_y(P(y), y^d P(xy)) has all ratios of
    eigenvalues as roots. A rational algebraic root of unity has a cyclotomic
    minimal polynomial. Exact irreducible factorization detects the converse.
    """
    x, y = sp.symbols("x y")
    d = matrix.rows
    p = matrix.charpoly(y).as_expr()
    ratio = sp.Poly(sp.resultant(p, sp.expand(y**d * p.subs(y, x*y)), y), x, domain=sp.QQ)
    for factor, _multiplicity in sp.factor_list(ratio)[1]:
        if not factor.monic().is_cyclotomic:
            return str(factor.monic().as_expr()), str(p), str(ratio.monic().as_expr())
    return None


def search(generators, max_length, max_nodes):
    alphabet = [(i + 1, g) for i, g in enumerate(generators)]
    alphabet += [(-(i + 1), g.inv()) for i, g in enumerate(generators)]
    identity = sp.ImmutableMatrix.eye(generators[0].rows)
    queue = deque([(identity, ())])
    seen = {identity}
    checked = 0
    while queue:
        matrix, word = queue.popleft()
        checked += 1
        if word:
            witness = noncyclotomic_ratio(matrix)
            if witness:
                factor, charpoly, ratio = witness
                return {"result": "infinite_projective_image", "word": word,
                        "characteristic_polynomial": charpoly,
                        "ratio_polynomial": ratio, "noncyclotomic_factor": factor,
                        "checked_matrices": checked}
        if len(word) == max_length:
            continue
        for label, generator in alphabet:
            product = sp.ImmutableMatrix(matrix * generator)
            if product in seen:
                continue
            if len(seen) >= max_nodes:
                return {"result": "inconclusive_node_limit", "checked_matrices": checked}
            seen.add(product)
            queue.append((product, word + (label,)))
    return {"result": "inconclusive", "checked_matrices": checked}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="JSON file with exact rational matrices")
    parser.add_argument("--max-length", type=int, default=4)
    parser.add_argument("--max-nodes", type=int, default=1000)
    args = parser.parse_args()
    if args.max_length < 1 or args.max_nodes < 2:
        parser.error("max-length must be positive and max-nodes at least 2")
    try:
        result = search(read_generators(args.input), args.max_length, args.max_nodes)
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError, json.JSONDecodeError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
