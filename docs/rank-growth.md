# Rank growth in the Anyon Atlas

Snapshot: Anyon Atlas export manifest generated 2026-10-15, source fingerprint
`4e30d91d46ef0faac774a1e38c6640d6afb604214c44f8c22a81a960c237861a`.
Source: [The Anyon Atlas, arXiv:2610.25439, Table 1 and Sections 3–4](https://arxiv.org/abs/2610.25439),
[export manifest](https://anyonatlas.org/export-v1/manifest.json), and
[Atlas conventions](https://anyonatlas.org/documentation). Run
`python3 scripts/rank/atlas_growth.py` from the repository root to regenerate.
It downloads identifier chunks into ignored `scratch/`, verifies their SHA-256
against the manifest, and checks per-chunk and total counts.

The table covers all 18,332 bosonic records, including Galois conjugates. For
maxima we select those with numerically real and strictly positive unit-row
quantum dimensions (tolerance 1e-8); the counts agree exactly with the
pseudo-unitary counts in Table 1 of the paper. This numerical proxy is not a
proof of positivity. Atlas entries are candidate modular data; a record is not
a proof that a category realizing it exists. Maxima are over this finite
catalog and can rise when the catalog changes. The global dimension is D²;
total quantum dimension is D = sqrt(D²). Values are rounded, and IDs identify
one maximizing record, with ties resolved by export order.

| Rank | All records | Positive-row records | Max D² | Max D | Example ID |
| ---: | ---: | ---: | ---: | ---: | :--- |
| 1 | 1 | 1 | 1.000000 | 1.000000 | B01-00000 |
| 2 | 8 | 4 | 3.618034 | 1.902113 | B02-00000 |
| 3 | 24 | 12 | 9.295897 | 3.048917 | B03-00002 |
| 4 | 55 | 18 | 19.234422 | 4.385707 | B04-00002 |
| 5 | 26 | 10 | 35.342421 | 5.944949 | B05-00010 |
| 6 | 192 | 50 | 100.617045 | 10.030805 | B06-00157 |
| 7 | 96 | 28 | 135.778913 | 11.652421 | B07-00006 |
| 8 | 294 | 63 | 308.434588 | 17.562306 | B08-00105 |
| 9 | 299 | 81 | 668.553755 | 25.856406 | B09-00143 |
| 10 | 332 | 76 | 1435.541753 | 37.888544 | B10-00112 |
| 11 | 158 | 44 | 1964.590777 | 44.323704 | B11-00119 |
| 12 | 1310 | 227 | 3926.660654 | 62.663072 | B12-00057 |
| 13 | 398 | 86 | 6712.525019 | 81.930001 | B13-00355 |
| 14 | 856 | 150 | 9783.522072 | 98.911688 | B14-00150 |
| 15 | 1050 | 204 | 10300.710197 | 101.492414 | B15-00714 |
| 16 | 1581 | 232 | 11227.844617 | 105.961524 | B16-00129 |
| 17 | 507 | 137 | 24276.516309 | 155.809231 | B17-00402 |
| 18 | 3286 | 536 | 521634.968896 | 722.243012 | B18-02829 |
| 19 | 402 | 70 | 13425.050037 | 115.866518 | B19-00243 |
| 20 | 2584 | 380 | 154290.120661 | 392.797811 | B20-02148 |
| 21 | 2708 | 454 | 59504.512099 | 243.935467 | B21-00898 |
| 22 | 2165 | 357 | 325181.434370 | 570.246819 | B22-00332 |

A plot of log(count) against rank rises overall but has large dips at prime
ranks and spikes at composite ranks; rank 18 has 3,286 records while rank 19
has 402. A plot of log(max D) against rank is broadly increasing but has a
striking rank-18 spike and falls at rank 19. Thus neither exact-rank sequence
is monotone, and the rank-18 record B18-02829 dominates the local maximum.
B11-00119 is the rank-11 maximum in this snapshot and is one of the exotic
examples discussed in Section 5 of the Atlas paper.

For descriptive comparison only, ordinary least squares on all 22 ranks
fits log(y) = a + b r and log(y) = a + b log(r), with equal weight per rank.
The fitted coefficients, and R² on the log scale, are:

| Quantity y | Exponential fit | R² | Power fit | R² |
| :--- | :--- | ---: | :--- | ---: |
| All records | 10.440 exp(0.281 r) | 0.778 | 1.325 r^2.402 | 0.914 |
| Maximum D | 1.558 exp(0.277 r) | 0.939 | 0.326 r^2.159 | 0.912 |

These are in-sample regressions, not evidence that either asymptotic law
holds: the samples are sparse, correlated through product constructions, and
subject to the Atlas search and reconstruction limits. In particular, no
upper bound on all categories follows from a catalog maximum. Exact field
arithmetic and realization certificates are required before turning a
numerical catalog inequality into a Lean theorem.

The distinction between D and D² is material: for example, the rank-18
maximum is approximately 722.243 for D and 521,634.969 for D². The observed
inequality D² < 2^(r+1) happens to hold for each displayed maximum, but the
rank-18 value is very close to the cutoff; this is a fragile observation, not
a proposed universal conjecture.

For the representation-theoretic program, [Ng–Schauenburg,
arXiv:0806.2493, Theorem 6.8](https://arxiv.org/abs/0806.2493) gives level N
for the *projective* representation, where N is the order of the unnormalized
twist T. A linear lift can instead have level dividing 12N
([Dong–Lin–Ng, arXiv:1201.6644, Theorem 2.3](https://arxiv.org/abs/1201.6644)).
[Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Proposition 3.15](https://arxiv.org/abs/1310.7050)
bounds N by 2^(2r/3+8) 3^(2r/3). These facts do not bound the number of
choices of vacuum and modular data inside a representation class, and do not
by themselves supply a dimension bound. Category equivalence and numerical
modular-data equivalence are also different: distinct categories can share
modular data.

## A quantitative first step and the remaining interfaces

For a finite group G, complex representations of dimension r are semisimple.
There are at most |G| irreducibles, and each multiplicity is at most r, so
there are at most (r+1)^|G| isomorphism classes of r-dimensional
representations. `MTC.Modular.Data.card_multiplicityProfile` proves the elementary
profile count; applying it requires formalizing semisimplicity, irreducible
classification, and the correspondence between profiles and representations.

If the unnormalized twist order N is at most L, every linear lift of the
projective modular representation has kernel containing Γ(12N), by the cited
lifting theorem. A lift therefore factors through SL(2, Z/(12N)Z), which has
at most (12N)^4 elements. Consequently a coarse bound on the number of
projective equivalence classes arising with N ≤ L is

    sum_{N=1}^L (r+1)^((12N)^4).

This counts representations up to arbitrary change of basis; the bound is
very loose and is not yet formalized in Lean. The source of the effective
rank-dependent level bound is Proposition 3.15 cited above. A specific datum
also chooses a vacuum and a simple-object basis. A further effective bound on
the number of distinct modular data up to simultaneous permutation of labels,
within one projective representation class, would control the numerical-data
fiber. Finiteness alone for realizable data follows abstractly from the
rank-finiteness theorem; the effective quantitative fiber bound is the
unresolved target. Bounding categories requires an additional bound on
inequivalent realizations of the same data or fusion rules; modular data do
not determine a category in general.
