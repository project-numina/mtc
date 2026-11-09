# Verification of the later pivotal manuscript

The new target definitions and their proofs cover the nondegenerate and degenerate pivotal
theorems, the centre and normalization lemmas, the pseudo-unitary-conjugate
corollary, closure, and the eventual infinite-image corollary.

The target review checked that nondegeneracy is categorical transparency,
that the degenerate positivity condition agrees with positivity on actual
transparent simple objects in the generated adjoint category, and that the
objectwise target uses the constructed generated braided fusion category.
Galois conclusions quantify over every conjugate represented by the project's
semilinear braided equivalence structure. The closure proof uses actual braid
images, categorical colored crossings, pure braids, finite direct sums and
retracts. The general pivotal numerical centrality argument is proved without
assuming a positive spherical structure. The original Property F statement
and `weaklyIntegral_of_propertyF` are unchanged from baseline `56dd74cd`.

A separate source-level review during the `fb6ec518` cleanup compared all six
pivotal targets, the generated-category definitions, the braid-image
construction and Galois assumptions with the supplied manuscript. It found
that the generated category is the actual full subcategory of retracts of
finite sums of tensor powers and that the objectwise statement retains the
simple-object, generated-category and eventual-infinite-image conditions.
Two convention bridges remain outside that review's formal scope: the target
quantifies over semilinearly represented conjugates, without constructing an
algebraic-model conjugate for every automorphism or proving equivalence with
all manuscript Galois conventions; and braid images are defined by the
concrete adjacent-generator subgroup on `n + 2` strands, without a separate
formal identification with the range of an Artin-group representation. The
index shift does not change the eventual quantifier. These are limitations of
the existing modeling, not new cleanup assumptions.

At proof commit `48e72d75`, with `LEAN_NUM_THREADS=4`:

- `scripts/check.sh` passed, auditing 5,258 integrated declarations without
  `sorryAx` or custom axioms, and 5,270 declarations across the project.
- `scripts/audit-target.sh` passed; the target dependency audit reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- An explicit `#print axioms` was run for all 908 public theorem declarations
  in the changed Lean modules. Each output contained only those three axioms
  or a subset. This includes the unconditional main, closure, and objectwise
  theorems. The conjecture collection has since been removed; every library declaration is audited.

The cleanup integration reran `scripts/check.sh` and `scripts/audit-target.sh`
with `LEAN_NUM_THREADS=4`; both passed. An explicit per-source-theorem axiom
listing checked 1,590 public theorems; the all-declaration kernel audit checked
5,251 project declarations. The fixed-cohort comparison, deleted construction
helpers, warning comparison and retained exceptions are recorded in the
[cleanup notes](style/cleanup-notes.md).

The proof and audit do not assert the existence of a particular external
realization for every abstract field automorphism; the Galois statement applies
to every semilinearly represented conjugate in the existing framework.
