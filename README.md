# Modular tensor categories in Lean

This project is building a crowdsourced Lean 4 and Mathlib library for modular tensor categories
(MTCs), related categorical structures, and anyon data. It combines formalized theorems, precisely
stated research problems and exact computational data so that people and AI systems can formulate,
test and prove mathematical statements. It is inspired by
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) and the
[Equational Theories Project](https://github.com/teorth/equational_theories).

## A formalized theorem

The existing [PropertyF](PropertyF.lean) library proves that a braided fusion category with a
pseudo-unitary Galois conjugate and property F is weakly integral. The theorem is
`PropertyF.Ground.target` in [Final.lean](PropertyF/Ground/Final.lean), using the definitions in
[Target.lean](PropertyF/Ground/Target.lean). The proof is complete and its audit reports precisely
`[propext, Classical.choice, Quot.sound]`. The text of the paper is in [paper/](paper/).

Property F means that the relevant braid group representations have finite image; weak integrality
means that the global Frobenius–Perron dimension is an integer. The converse is the open direction
of the Naidu–Rowell property F conjecture. Its investigation, including the distinction between
modular data and categories realizing them, is one of the project's research goals.

## Problems and data

- [MTC/](MTC/) contains shared definitions and proved theorems, without `sorry`.
- [Conjectures/](Conjectures/) contains open problems and known results awaiting formalization.
  The [dashboard](docs/STATUS.md) lists their status and sources; the
  [conjecture template](Conjectures/README.md) explains the metadata.
- [AnyonAtlas/](AnyonAtlas/) contains generated, exact data when available, without `sorry`.
  Data-checkable claims should specify their actual scope and evidence. Modular data alone do not
  establish the existence of an MTC or its property F.
- [PropertyF/](PropertyF/) contains the existing proof, pending a later library reorganization.

Research directions include property F and weak integrality, realizability of modular data via
pentagon and hexagon equations, non-Chern–Simons examples, Galois orbits and condensations, and
quantitative bounds on modular data at fixed rank.

[The Anyon Atlas](https://anyonatlas.org/) is due to Jonah Berean-Dutcher, Clay Córdova, Julio
Parra-Martinez and Richard Tuddenham; see their [paper](https://arxiv.org/abs/2610.25439). It
catalogues modular and supermodular data and supplies exact data and selected F- and R-symbols.
The paper establishes realizability of selected rank-11 and rank-12 examples outside its explored
Chern–Simons constructions. Respect the source's terms when obtaining or redistributing data.

## Build and contribute

Lean and Mathlib are pinned to v4.35.0. In a fresh clone with the Lean toolchain installed:

```sh
lake exe cache get
scripts/check.sh
scripts/audit-target.sh
```

The checks build all libraries, audit axioms of project declarations and the frozen target, and
verify the generated dashboard. `scripts/check.sh` defaults to CPU cores 0–3; set
`PROPERTYF_AUDIT_CORES` to a valid CPU list on your machine if needed. See
[CONTRIBUTING.md](CONTRIBUTING.md) for claiming problems, submissions and AI contributions.
