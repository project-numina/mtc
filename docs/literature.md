# Fusion categories and modular data: literature catalog

Survey date: 2026-10-28. Status refers to the mathematical literature, not to
Lean. “Solved” means a theorem is available in the cited source; it does not
mean that the repository has formalized it. “Open” means the cited question is
an active target, subject to later literature checks. Formalization difficulty
is a rough assessment: **low** means arithmetic on an established exact data
interface, **medium** means substantial algebra or finite group machinery, and
**high** means new categorical infrastructure or long classification proofs.

The existing `PropertyF.Ground` interface represents braided fusion categories
and defines FP dimensions using spectral radii. Its own documentation records
that identification with standard categorical invariants is pending. It does not
yet provide a general (not necessarily braided) fusion category, modularity,
pivotal structures, centers, module categories, or weak group-theoreticity.
Claims below should not be encoded with unconstrained stand-in predicates. The
Lean files in `MTC/Conjectures/Fusion` are braided restrictions of source results,
and their translation to the frozen interface is part of the proof obligation.

## Arithmetic and structure

1. **Weakly group-theoretical question — open.** Does a weakly integral fusion
   category exist that is not weakly group-theoretical? An affirmative answer
   would disprove the often-conjectured universal implication. Weakly
   group-theoretical means Morita equivalent to a nilpotent fusion category;
   it is not synonymous with group-theoretical. ENO, [Question 2 and Definition
   1.1](https://arxiv.org/html/0809.3031). **High:** extensions, gradings,
   Morita equivalence, and centers. A candidate counterexample to property F
   would need this obstruction because weakly group-theoretical braided fusion
   categories have property F; see [Green–Nikshych](https://arxiv.org/abs/1911.02633).
2. **Strong Frobenius question — open.** Does every fusion category have the
   strong Frobenius property? This quantifies over indecomposable module
   categories and uses a specified normalization of module FP dimensions. ENO,
   [Definition 1.4 and Question 1](https://arxiv.org/html/0809.3031).
   **High:** module categories and algebraic integers. Weakly group-theoretical
   categories satisfy it (Theorem 1.5).
3. **Kaplansky and Frobenius divisibility — open in general.** The ordinary
   Frobenius property asks whether `FPdim(C)/FPdim(X)` is an algebraic integer
   for each simple `X`; this generalizes the sixth Kaplansky conjecture for
   semisimple Hopf algebras. See ENO, [Definition 1.4 and Theorem
   1.5](https://arxiv.org/html/0809.3031). **High:** general fusion and FP
   dimension. Do not confuse it with squared divisibility below.
4. **Modular squared divisibility — solved.** In a modular category,
   `dim(C)/dim(X)^2` is an algebraic integer for every simple `X`; see
   [Etingof–Gelaki–Nikshych–Ostrik, Proposition 8.14.6](https://math.mit.edu/~etingof/egnobookfinal.pdf).
   In an integral modular category the positive FP dimensions are integers,
   so the square divides the global FP dimension as an integer. **High** for
   the categorical theorem; **low** to check the integer consequence on exact
   integral Atlas records. The analogous stronger claim for arbitrary braided
   or nonbraided fusion categories must not be assumed.
5. **Categorical Burnside theorem — solved.** Fusion categories of FP dimension
   `p^a q^b` are solvable, for primes `p,q` and nonnegative exponents. ENO,
   [Theorem 1.6](https://arxiv.org/html/0809.3031). **High:** solvability,
   extensions and Morita theory; an Atlas dimension filter is low difficulty.
6. **Small weakly integral categories — solved for stated bounds.** Every
   weakly integral fusion category of FP dimension less than 120 is solvable
   or group-theoretical; every weakly integral braided fusion category of FP
   dimension less than 1800 is weakly group-theoretical. See Dong,
   [arXiv:2103.04553](https://arxiv.org/abs/2103.04553). **High:** classification;
   dimension tests alone do not certify the categorical conclusion.
7. **Odd weak dimension — solved.** Odd integer FP dimension forces all simple
   FP dimensions to be integers. See DGNO, [Corollary 2.22](https://arxiv.org/html/0906.0620).
   **High:** grading theory; the numerical conclusion is Atlas-checkable.
8. **Weak dimension and squared simple dimensions — solved.** For weakly
   integral fusion categories each simple squared FP dimension is an integer,
   and the square classes yield a grading. Ising has dimensions `1,1,√2`, so
   weak integrality is strictly weaker than integrality. DGNO, [Proposition
   2.18 and Remark 2.19](https://arxiv.org/html/0906.0620). **Medium–high:**
   Perron theory and gradings; numerical checks are low difficulty.
9. **FP dimensions and positivity — solved.** Simple FP dimensions are
   algebraic integers at least one; their squared sum is a positive algebraic
   integer. See DGNO, [Section 2.4.1](https://arxiv.org/html/0906.0620).
   **Medium:** fusion rings, finite matrices, and Perron theory.
10. **Weak integrality implies pseudo-unitarity — solved.** Global categorical
    and FP dimensions coincide; there is a positive spherical structure with
    simple dimensions equal to FP dimensions. DGNO, [Proposition 2.18 and
    Corollary 2.24](https://arxiv.org/html/0906.0620). **High:** traces,
    squared norms, and pivotal structures. The ground encoding needs the
    independent identification noted at the beginning of this catalog.
11. **Pivotal structure problem — open.** Does every fusion category admit a
    pivotal structure? DGNO, [Section 2.4.3](https://arxiv.org/html/0906.0620)
    describes this as conjectural. **High:** monoidal natural isomorphisms
    between the identity and double dual; do not confuse the objectwise
    isomorphism supplied by a braiding with a pivotal monoidal isomorphism.

## Modular representations, Galois theory and indicators

12. **Cauchy theorem — solved.** For a modular category with `N = ord(T)`,
    the prime ideals dividing global quantum dimension and `N` coincide in
    `ℤ[ζ_N]`. This is a statement about prime ideals, not generally about
    divisibility of an integer quantum dimension. Bruillard–Ng–Rowell–Wang,
    [Theorem 3.9](https://arxiv.org/html/1310.7050). **High:** cyclotomic
    integers and modularity; an integral numerical consequence can be checked
    using exact Atlas data.
13. **Congruence property — solved.** Modular representations have congruence
    kernels and hence finite image, with normalization and level specified in
    the theorem. Ng–Schauenburg, [arXiv:0806.2493](https://arxiv.org/abs/0806.2493).
    **High:** representations of `SL(2,ℤ)`, principal congruence subgroups and
    categorical indicators. This concerns modular-group representations and
    is not property F for braid-group representations.
14. **Galois permutations — solved.** Galois automorphisms permute the columns
    of normalized `S` through the characters `Sᵢⱼ/S₀ⱼ`; there are associated
    signs. For a normalized pair `(s,t)`, `σ²(tᵢ)=t_{σ̂(i)}`. See
    Bruillard–Ng–Rowell–Wang, [Section 2.2.4 and Theorem 2.9](https://arxiv.org/html/1310.7050).
    **Medium–high:** exact cyclotomic fields and label permutations; suitable
    for exact finite-data checks after normalization is specified.
15. **Galois extension bound — solved.** For a normalized modular pair,
    the Galois group of the field generated by `t` over that generated by `S`
    is an elementary 2-group. See [Lemma 2.10](https://arxiv.org/html/1310.7050).
    **Medium–high:** finite Galois extensions and normalization.
16. **Frobenius–Schur periodicity — solved.** Higher indicators are periodic
    for spherical fusion categories, and their exponent is the order of the
    twist of the Drinfeld center. Ng–Schauenburg,
    [arXiv:math/0601012](https://arxiv.org/abs/math/0601012). **High:**
    pivotal traces and centers; modular-data formulas offer a finite check.
17. **Second indicator — solved.** For a simple object in a modular category,
    the second indicator is zero if it is not self-dual, and is `+1` or `-1`
    if it is self-dual. See [Section 2.2.5](https://arxiv.org/html/1310.7050).
    **Medium–high:** duality and indicator conventions. The exact formula in
    the same section is a useful Atlas check when fusion and twist data exist.
18. **Twist roots of unity — solved.** Vafa's theorem implies finite twist
    order in a modular category. See Etingof,
    [arXiv:math/0207007](https://arxiv.org/abs/math/0207007). **High:**
    categorical proof; low for exact encoded twists.

## Extensions, classification and realization

19. **Minimal modular extensions — solved.** Every slightly degenerate braided
    fusion category has a minimal nondegenerate extension; in particular every
    pseudo-unitary super-modular category has a minimal modular extension.
    Johnson-Freyd–Reutter, [arXiv:2105.15167](https://arxiv.org/abs/2105.15167).
    **Very high:** fusion 2-categories and extensions. Existence is no longer
    an open conjecture; constructive descriptions remain useful.
20. **Rank finiteness — solved; effective growth — open.** There are finitely
    many modular categories of fixed rank up to equivalence; an explicit useful
    growth bound for maximum dimension is a separate question. See
    [arXiv:1310.7050](https://arxiv.org/abs/1310.7050), especially Section 4.
    **High:** equivalence classes, modular representations and arithmetic.
    Atlas maxima provide lower bounds on any proposed upper bound, not a proof
    of maximality among all categories.
21. **Low rank classification — solved within stated scope.** Rowell–Stong–Wang,
    [arXiv:0712.1377](https://arxiv.org/abs/0712.1377), classify unitary MTCs
    through rank 4; Bruillard–Ng–Rowell–Wang,
    [arXiv:1507.05139](https://arxiv.org/abs/1507.05139), determine fusion
    rules and monoidal equivalence classes at rank 5. **Very high:** explicit
    categories and equivalences. Keep unitary, braided, and monoidal
    equivalence conventions distinct.
22. **Integral modular data at small rank — solved within stated scope.**
    Alekseyev–Bruns–Palcoux–Petrov, [arXiv:2302.01613](https://arxiv.org/abs/2302.01613),
    classify integral modular data through rank 13 and integral half-Frobenius
    fusion rings through rank 12. Their perfect integral modular categories
    through rank 13 are trivial. **High:** exact classification and ensuring
    data axioms match; enumeration certificates are a useful intermediate goal.
23. **Integral dimension `pq²` — solved.** Jordan–Larson classify integral
    fusion categories of FP dimension `pq²` for distinct primes; not all such
    categories are group-theoretical. [arXiv:0812.1603](https://arxiv.org/abs/0812.1603).
    **Very high:** extensions and category equivalence.
24. **Modular data do not classify categories — disproved uniqueness.**
    Mignard–Schauenburg construct arbitrarily many pairwise inequivalent
    modular categories sharing the same modular data, from twisted doubles of
    finite groups: [arXiv:1708.02796](https://arxiv.org/abs/1708.02796).
    **Very high:** twisted doubles, modular data and inequivalence. This does
    not imply that arbitrary formal modular data are realizable.
25. **Realizability of modular data — open in general.** Necessary modular-data
    identities alone do not by themselves construct a fusion category. An exact
    realization should give associator and braiding data and verify pentagon
    and hexagon, with gauge equivalence specified. The [Anyon Atlas](https://arxiv.org/abs/2610.25439)
    reports explicit solutions for its 11- and 12-anyon examples. **High:** exact
    algebraic numbers, gauge and coherence. The paper says the non-Chern–Simons
    examples *do not appear* to arise by the stated constructions; treat that
    claim with its qualification, and do not assume each modular-data record
    already has a category realization.
26. **Witt group — solved structural results; classification open-ended.**
    Centers are characterized by Lagrangian algebras and define the zero
    class in the Witt group of nondegenerate braided fusion categories.
    Davydov–Müger–Nikshych–Ostrik, [arXiv:1009.2117](https://arxiv.org/abs/1009.2117).
    The super Witt group and the `ℤ/16` kernel generated by Ising categories
    are studied in [arXiv:1109.5558](https://arxiv.org/abs/1109.5558).
    **Very high:** étale algebras, centers, Deligne products and quotients.
27. **Ocneanu rigidity — solved.** Fusion categories and tensor functors are
    undeformable; the theorem yields finiteness for fixed fusion rules under
    its hypotheses. ENO, [On fusion categories](https://annals.math.princeton.edu/2005/162-2/p01).
    **Very high:** deformation complexes and algebraic geometry. It does not
    itself give a bound on the possible fusion rules at a fixed rank.
28. **Müger centralizer and factorization — solved.** For a fusion subcategory
    `K` of a modular category `C`, its double centralizer is `K`, and
    `dim(K) dim(K′) = dim(C)`. A modular subcategory gives a product
    factorization. Müger, [arXiv:math/0201017](https://arxiv.org/abs/math/0201017).
    **High:** full fusion subcategories, centralizers and dimensions.


29. **Simple FP dimensions as d-numbers — open question.** Is the FP
    dimension of each simple object of a braided fusion category a d-number?
    Ostrik, [Remark 1.9(i)](https://arxiv.org/html/0810.3242), asks this;
    Remark 1.9(ii) records a nonbraided counterexample. **Medium–high:**
    algebraic integers and Galois actions; exact candidate dimensions can be
    checked using minimal-polynomial criteria. Status is based on this source
    and a literature search, not a proof that no later solution exists.
30. **Galois-stable dimension ideals — solved.** Global FP dimension is a
    d-number for any fusion category, and each simple categorical squared norm
    is a d-number in the braided case. Ostrik,
    [Corollary 1.3 and Theorem 1.8](https://arxiv.org/html/0810.3242).
    **High:** interpreting categorical squared norms and the Galois action;
    numerical exact checks are substantially easier.

## Problem-list guides and Atlas scope

Rowell–Wang, [Mathematics of Topological Quantum Computing](https://arxiv.org/abs/1705.06206),
connects classification and property F with braid images and computational
power. Rowell–Stong–Wang, [arXiv:0712.1377](https://arxiv.org/abs/0712.1377),
provides a classification program and its problems. The AIM
[2012 workshop summary](https://aimath.org/pastworkshops/fusioncatrep.pdf)
records classification by rank, dimension and small prime support, exotic
examples, indicators and Witt theory; it links the
[workshop problem list](http://aimpl.org/fusioncat). That list was not
accessible during this survey, so its individual questions and current status
have not been independently checked here.

The Atlas is a catalog of modular and supermodular **data**. Exact record
verification can establish numerical identities for the encoded finite set,
but does not by itself prove existence of a category, unitarity, or a universal
classification statement. No blanket Atlas verification is claimed here.
