# Formalization status

Work in progress. The entire paper has been read and mapped in `PLAN.md`.

Implemented and kernel checked:

- Actual tensor powers, adjacent categorical braidings with associators, and
  property F as finiteness of their generated image subgroups.
- Complex unitary matrix trace bound and its scalar equality case, including
  zero-dimensional blocks.
- Weighted traces on explicit products of matrix algebras; the sign involution
  and centrality forced by trace saturation.
- Lemma 3.1 from explicit semisimple multiplicities and primitive partial-trace
  laws: the overlapping products, recurrence, estimates and unbounded-powers
  argument are all proved.
- Lemma 3.2 from two-/three-strand primitive partial-trace laws, the self-braiding
  trace, nonzero weights and finite order. The attained trace and centrality are
  proved, not assumed. Nonzero weights under Galois transport are also proved.
- Proposition 2.1, including self-duality and both displayed identities, from
  standard modular-data identities.
- The positive dimension-ratio calculation and final Galois inequality
  contradiction.

**These are interface-relative proofs.** The construction of the interfaces
from fusion categories, Lemma 4.1, closure, and the full main theorem are still
outstanding. No completed categorical theorem is claimed at this stage.

Lean and Mathlib are pinned to `v4.35.0`. Mathlib's 9031 cached artifacts were
downloaded with `LEAN_NUM_THREADS=8 taskset -c 0-7 lake exe cache get`.

The first skeleton used the monolithic `Mathlib` import, which exceeded a 1400 MB
per-process limit. It now uses selective imports. No Mathlib source build is
needed. The repository's original prompt and runner are preserved.

## Assumption ledger

No custom axiom declarations or `sorry` proofs have been introduced.
All unproved interface laws are in `PropertyF/Axioms.lean`:

| Interface | Inputs | Source and status |
|---|---|---|
| `MultiplicityData` | Finite multiplicities, real dimensions, FP bounds | Maschke/Artin–Wedderburn and [ENO §8, 8.21]; not constructed from categorical data |
| `OverlapModel` | Star algebra embeddings, partial-trace bimodularity, simple-strand scalar partial trace, FP multiplicity sum | Spherical calculus [EGNO §§4.7–4.8], Schur's lemma, FP dimension character; not constructed from categorical data |
| `ModularData` | Symmetry, unit column, S-square, distinct fusion-character Galois permutation | [EGNO 8.13.11, 8.14.2]; actual finite matrices and complex field automorphisms |
| `ThreeStrandModel` | Braiding relation, pair embeddings, two partial traces, nonzero pair algebra, finite order | Spherical calculus [EGNO §§4.7–4.8] and finite braid images; not constructed from categorical data |

The last three interfaces contain genuine hypotheses. `#print axioms` does not
list theorem parameters, so an empty custom-axiom list does not discharge them.
The nonzero-weight condition and `Tr(c²)=df` are explicit arguments to the
rigidity theorem, not unmentioned consequences of the model.

## Paper audit

No mathematical error has yet been established. In particular, the existing
Mathlib centre construction does not supply the fusion/modular results used on
page 5. Those results must not be mistaken for already formalized infrastructure.

## Build

```sh
LEAN_NUM_THREADS=8 taskset -c 0-7 lake exe cache get
bash scripts/check.sh
```

The script pins CPU affinity to cores 0–7. The Lake configuration limits each
Lean elaborator to two threads and 3000 MB. Resource limits will be adjusted
within the requested aggregate budget if necessary.
