# Modular tensor categories in Lean

[The Anyon Atlas](https://anyonatlas.org/) catalogues more than 25,000 modular and supermodular
data, with exact values and selected F- and R-symbols. This project uses that data as a testing
ground for AI-assisted mathematics: modelling the data in Lean 4, formulating conjectures about it,
and proving or disproving them.

- [MTC/](MTC/) provides the definitions and theorems needed to do this: fusion and braided fusion
  categories, Frobenius–Perron dimensions, the Drinfeld centre, modular data, and F- and
  R-symbols. It contains no `sorry`.
- [Conjectures/](Conjectures/) contains Lean formulations of open conjectures in this area, one per
  file. The [dashboard](docs/STATUS.md) lists each conjecture with its status and source.
- [AnyonAtlas/](AnyonAtlas/) contains the exact Lean encoding of Atlas records. The
  [data guide](AnyonAtlas/README.md) explains how to download, validate and generate the data.

**Open a pull request** with a proof or disproof of a conjecture, or with a new conjecture. See
[CONTRIBUTING.md](CONTRIBUTING.md).

## A proof of property F implies weak integrality

The Naidu–Rowell conjecture states that a braided fusion category has property F (every braid group
representation it defines has finite image) if and only if it is weakly integral (its global
Frobenius–Perron dimension is an integer). This library proves one direction: **every braided
fusion category with property F and a pseudo-unitary Galois conjugate is weakly integral**. This
covers every unitary modular tensor category, and hence every entry of the Atlas.

The theorem is `PropertyF.Ground.target` in [Final.lean](PropertyF/Ground/Final.lean). The proof
is complete and depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The
manuscripts and a map from their results to Lean declarations are in
[papers/property-f-weak-integrality](papers/property-f-weak-integrality/). The converse direction
remains open and is stated in [Conjectures/PropertyF](Conjectures/PropertyF/).

## The Anyon Atlas

The Atlas is due to Jonah Berean-Dutcher, Clay Córdova, Julio Parra-Martinez and Richard Tuddenham
([arXiv:2610.25439](https://arxiv.org/abs/2610.25439)). Cite the paper and the record ID when using
an entry. Modular data alone do not establish that a category realizing them exists, so a claim
about the data should state its scope precisely.

## Building

Lean and Mathlib are pinned to v4.35.0. In a fresh clone with the Lean toolchain installed:

```sh
lake exe cache get
scripts/check.sh
scripts/audit-target.sh
```

These build the libraries, audit the axioms of every declaration, and check the dashboard.
`scripts/check.sh` uses CPU cores 0–3 by default; set `PROPERTYF_AUDIT_CORES` to change this.
