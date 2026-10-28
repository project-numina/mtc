#!/usr/bin/env python3
"""Exact weak-integrality check for Atlas B11-00119, paper (5.2)-(5.3).

Requires SymPy. The paper uses an unnormalized S matrix with vacuum entry 1;
its first row gives the quantum dimensions of this unitary categorification.
See https://arxiv.org/html/2610.25439v1#S5 .
"""
import sympy as sp

z = sp.Symbol("z")


def c(n):
    """zeta_35^n + zeta_35^-n as a polynomial in zeta_35."""
    return z ** (n % 35) + z ** (-n % 35)


a = 2 + c(4) + c(6) - c(8) + c(9) - c(12) - c(14) - c(17)
b = 2*c(2) + 2*c(3) + c(4) + c(6) + c(9) + 2*c(13) - 3*c(14)
cc = b - c(14)  # c_5^2 = c_35^14
d = cc + 1
e = 2 + 3*c(2) + 3*c(3) + 2*c(4) + 2*c(6) + 2*c(9) + 3*c(13) - 4*c(14)
f = e + c(7)  # c_5^1 = c_35^7
squared_dimension = 1 + 3*a**2 + b**2 + cc**2 + 3*d**2 + e**2 + f**2
phi = sp.cyclotomic_poly(35, z)
remainder = sp.Poly(sp.rem(squared_dimension, phi, z), z, domain=sp.QQ)
assert remainder.degree() < sp.totient(35)
assert remainder.degree() > 0
print("Atlas B11-00119, global dimension D²:")
print("Cyclotomic polynomial:", phi)
print("Canonical remainder:", remainder.as_expr())
print("Numerical approximation:", sp.N(squared_dimension.subs(z, sp.exp(2*sp.pi*sp.I/35)), 14))
print("Nonconstant remainder proves D² is irrational, hence not weakly integral.")
