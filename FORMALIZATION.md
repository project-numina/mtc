# Formalization status

Conditional formalization. The entire paper has been read and mapped in `PLAN.md`.

The main theorem `PropertyF.propertyF_implies_weaklyIntegral` and the closure and
objectwise corollary compile with zero `sorry` proofs. They have explicit
literature and categorical realization hypotheses in `PropertyF/Axioms.lean`.
These hypotheses have not been constructed from Mathlib's category structures.
Consequently this is not an assumption-free categorical formalization.

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

**These are interface-relative proofs.** Also implemented:

- Finite semisimplicity and FP dimension as a positive fusion-ring character on
  genuine Mathlib complex linear rigid braided categories.
- Intrinsic global dimension from actual evaluation and coevaluation morphisms.
- Spherical pivotal-scalar algebraicity and finite-extension argument.
- Mutual-centralizer computations using actual half-braidings.
- Lemma 4.1's containment and property-F arguments from the explicit standard
  centre criterion and product quotient witnesses.
- The complete main contradiction, Galois reduction, and integer conclusion.
- Lemma 4.2's finite-product/finite-index argument from cabling witnesses, and
  Corollary 4.3 including propagation to every sufficiently large strand count.
- General finite-image quotient/restriction/product and inverse-generator
  transfer arguments from §2.1.

Remaining construction bridges are described in the expanded ledger below.
`PropertyF/Audit.lean` runs the main dependency checks during `lake build`.
The main theorem's `#print axioms` result is exactly
`[propext, Classical.choice, Quot.sound]`. Explicit theorem parameters do not
appear in that list.

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

Additional standard-input structures now include `CenterInputs`,
`ThreeStrandRealization`, `DimensionField`, `PseudoUnitaryInputs`, `StandardInputs`,
`CablingWitness`, and `GeneratedInputs`. Their full field-level ledger will be
recorded below before handoff.

These interfaces contain genuine hypotheses. `#print axioms` does not
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
