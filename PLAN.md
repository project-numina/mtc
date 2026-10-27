# Paper-to-Lean plan

The complete six-page paper was read before implementation. The target is Theorem
1.1 including the initial reduction to a pseudo-unitary Galois conjugate, not just
its pseudo-unitary special case. Literature inputs must remain distinguishable
from the paper's own arguments.

## Pinned environment and library audit

Lean `v4.35.0`; Mathlib tag `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Downloaded using
`lake exe cache get` (9031 artifacts); no Mathlib source compilation.

Checked the actual source at this revision:

| Subject | Mathlib source / available infrastructure | Remaining work |
|---|---|---|
| Monoidal, braided categories | `CategoryTheory/Monoidal/{Category,Braided/Basic,Linear}.lean` | Tensor powers and braid action with coherence |
| Linear and semisimple categories | `CategoryTheory/Linear/`, preadditive categories, biproducts, simple objects | Finite semisimplicity and fusion-category interface |
| Rigidity | `CategoryTheory/Monoidal/Rigid/{Basic,Braided}.lean` | Pivotal/spherical structure and partial trace calculus; pivotal categories are explicitly a TODO in `Rigid/Basic.lean` |
| Drinfeld centre | **Already exists:** `CategoryTheory/Monoidal/Center.lean`, including half-braidings, braided structure and canonical functor | Fusion, spherical and modular properties; dimension formula and centralizer theory |
| Braid groups | No braid-group presentation found by file/declaration search | Artin presentation, pure braids, cabling, strand inclusions |
| Finite group representations | `RepresentationTheory/{Basic,Maschke,Semisimple,Irreducible,Character,FinGroupCharZero}.lean` | Compatible averaged adjoint and simultaneous block decomposition |
| Ordinary trace | `LinearAlgebra/{Trace,Matrix/Trace}.lean`, `Analysis/InnerProductSpace/Trace.lean` | Weighted categorical trace; equality case for unitary matrices |
| Unitary matrices | `LinearAlgebra/UnitaryGroup.lean` | Trace estimate and equality case |
| Galois theory | `FieldTheory/Galois/{Basic,Infinite}.lean`, `AbsoluteGaloisGroup.lean`, algebraic closures | Galois conjugation of tensor categories and modular data |
| Number fields / algebraic integers | `NumberTheory/NumberField/`, `RingTheory/IntegralClosure/` | Descent of category and pivotal structure; total reality of spherical dimensions |
| Fusion rings and FP dimension | No fusion-category / FP-dimension implementation found | Explicit finite fusion data and Perron character, with cited existence/uniqueness inputs |
| Pseudo-unitarity, property F, weak integrality | No definitions found | Define from dimensions and actual finite images, not arbitrary propositions |
| Modular categories / modular data | No fusion-level implementation found | Finite S-matrix data and cited identities |

## Exhaustive paper map

| Paper location | Lean target / obligations |
|---|---|
| §1, braid images `G(X,n)` | Image subgroup of a representation of the Artin group |
| §1, property F | All objectwise braid-image subgroups finite for `n ≥ 2` |
| §1, weak integrality | Global FP dimension is the image of an integer |
| §1, pseudo-unitarity | Equality of global categorical and FP dimensions |
| Naidu–Rowell conjecture | State as a proposition for context; do not claim a proof of its converse |
| Theorem 1.1 | `propertyF_implies_weaklyIntegral`, conditional only on audited standard inputs |
| §2.1, summands and subcategories | Finite-image transfer by restriction / surjective image |
| §2.1, dominant functors | Combine quotient-image transfer with summand transfer |
| §2.1, reverse and Deligne product | Inverse generators; image in product of finite groups; dominance |
| §2.1, Galois invariance | Injective scalar transport of matrix relations plus fusion-rule invariance; number-field descent [ENO 2.30, 2.33] is an input |
| §2.2, categorical dimension, FP dimension, multiplicities | Real/complex dimension functions on simple labels and finite multiplicity sums |
| §2.2, reality, nonvanishing, spectral bounds, total positivity | Named literature inputs [ENO 2.3, 2.5, 2.10, 8.21] |
| §2.2, canonical spherical structure | Literature input [ENO 8.23] |
| §2.2, spherical structure descent remark | Algebraicity of pivotal scalar follows by dividing algebraic dimension by nonzero algebraic quantum trace; finite many scalars give finite extension |
| §2.3, S matrix, charge conjugation, characters | Finite matrices and a permutation action; standard identities [EGNO 8.13.11, 8.14.2] as inputs |
| Proposition 2.1 (1) | Substitute the Galois-transformed unit column |
| Proposition 2.1 (2), self-duality | Sum squares, use `S²=DE`, exclude vanishing, divide |
| §3, averaged adjoint and insertions | Finite group averaging and coefficientwise inverse/conjugate description; compatibility with algebra homomorphisms |
| Lemma 3.1 | Ordinary unitary trace estimate, weighted multiplicity estimate, overlapping-strand trace identity, unbounded-powers argument |
| Lemma 3.2, trace weights | Positive original weighted sums and injectivity of Galois automorphisms imply nonvanishing |
| Lemma 3.2, sign involution | Block diagonal matrices with signs of real weights; apply Lemma 3.1 |
| Lemma 3.2, braid `a²b²` | Two partial traces compute `d f²`; triangle equality forces scalar blocks |
| Lemma 3.2, braid algebra | Centrality of `a²b²` implies centrality of `a²`; conjugacy gives `a²=b²` |
| Lemma 3.2, conclusion | Partial trace gives scalar square braiding; finite order implies scalar has modulus one |
| Lemma 4.1, centre | Standard centre modularity and squared dimensions [EGNO 7.16.6, 8.20.14, 9.3.4] |
| Lemma 4.1, centralizers | Establish mutual centralizers, intersection, symmetric integrality [DGNO 2.46], S criterion and double centralizer [EGNO 8.20.5, 8.21.1] |
| Lemma 4.1, property F | Braided product functor onto its generated image and proved transfers |
| Theorem 1.1, contradiction | Non-PU conjugate has smaller positive global dimension; Proposition 2.1 gives dimension ratio in `(0,1)`; Lemma 3.2 contradicts FP dimension `≥1` |
| Theorem 1.1, arithmetic | All conjugates equal implies rationality; algebraic integrality implies integer |
| Lemma 4.2 | Positive tensor powers generate the rigid subcategory [EGNO 4.11.4]; pure-braid cabling, finite products, finite-index transfer [ERW 2.1(ii)] |
| Corollary 4.3 | Contraposition of closure and main theorem, squared FP dimensions [ENO 8.27], faithful strand inclusions propagate infinitude |
| Final unitary consequence | Fusion subcategories of unitary categories are pseudo-unitary |
| Final nonsimple caveat | Record distinction between simple squared FP dimension and direct sums |

## Proof policy

All categorical/representation-theoretic imports not proved here will be precise,
documented assumptions in one file, `PropertyF/Axioms.lean`, if used. Structural
interfaces are not to contain Lemmas 3.1, 3.2, 4.1 or the main theorem as fields.
The documentation must explicitly identify any unconstructed interface or
missing categorical bridge. A conditional numerical reduction is not, by itself,
a completed formalization of Theorem 1.1. `FORMALIZATION.md` records actual status,
not this plan's intentions.


## Implemented result and remaining scope

All numbered results now have checked **conditional** proofs: Proposition 2.1 in
`GaloisSymmetry.lean`, Lemmas 3.1 and 3.2 in `TraceBound.lean` and
`GaloisRigidity.lean`, Lemma 4.1 in `CenterBasics.lean` and `Center.lean`, Theorem
1.1 in `Main.lean`, and Lemma 4.2 / Corollary 4.3 in `Consequences.lean`.
`Transfer.lean`, `Descent.lean`, and `Arithmetic.lean` cover the auxiliary
arguments. `Audit.lean` is part of the default build.

The actual FP dimension definitions use positive fusion characters and Hom-space
multiplicities. Intrinsic global dimension uses evaluation/coevaluation and simple
double-dual isomorphisms. Galois conjugacy uses semilinear braided monoidal
equivalences. The braid image is defined directly as the subgroup generated by
adjacent categorical braidings, so no Artin presentation is required for its
finiteness predicate.

The construction of `StandardInputs` and `GeneratedInputs` is **not completed**.
Their precise assumptions, including the unconstructed averaged-star, partial
trace, centre-product and cabling diagrams, are listed field by field in
`FORMALIZATION.md`. The final prose unitary specialization has no implementation
of a unitary/C*-category structure, and the nonsimple caveat has no constructed
categorical counterexample. These remaining items must not be read as completed
merely from the lack of `sorryAx` dependencies.
