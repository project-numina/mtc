# Searching for infinite braid images

Naidu and Rowell, [arXiv:0903.4157, Conjecture 2.3](https://arxiv.org/abs/0903.4157), predict that weakly integral braided fusion categories have property F. Green and Nikshych prove property F for weakly group-theoretical braided fusion categories, [arXiv:1911.02633, Theorem 7.2](https://arxiv.org/abs/1911.02633). A counterexample therefore requires an actual weakly integral category, not merely unverified modular data, and cannot be weakly group-theoretical. Non-Chern–Simons status alone does not establish either property.

The Atlas global dimension is D² = sum of squared quantum dimensions, which for a unitary category is its global FP dimension. It is D², not D, that must be integral. [The Anyon Atlas](https://arxiv.org/abs/2610.25439), Section 5, supplies an exact S matrix for B11-00119 and reports a unitary categorification. Run `python3 scripts/propf/exotic_b11.py` to verify that its D² is irrational: the sum of squares of the vacuum row has a nonconstant remainder modulo the irreducible cyclotomic polynomial Φ₃₅. The value is approximately 1964.59077737424. This entry is excluded as a counterexample to weak integrality implies property F. No conclusion is asserted about all other entries or the rank-12 example.

The Atlas paper reports full F-symbol solutions for the rank-11 and rank-12 exotic orbits, but Section 5 says the details will appear separately. The website says that selected F- and R-symbols are available; exact availability for each relevant entry must be checked. Modular data do not by themselves determine the associator or the braid matrices. The Atlas search should filter exact D² for integrality, distinguish known weakly group-theoretical realizations from unknown ones, and then obtain valid exact F and R symbols for any remaining actual category. Where F/R data are unavailable, solving the pentagon and hexagon equations is a separate prerequisite.

## Exact matrix search

`braid_infinite.py` accepts a JSON object with a `generators` array, containing the consecutive generators σ₁, …, σₙ₋₁ as equally sized square matrices. Each entry must be an integer or a string containing an exact rational number such as `"-3/2"`. Install SymPy in the environment, then run:

```sh
python3 scripts/propf/braid_infinite.py matrices.json --max-length 4 --max-nodes 1000
python3 -m unittest discover -s scripts/propf -v
```

The script verifies invertibility and all Artin relations exactly. It enumerates distinct matrices represented by bounded words in generators and inverses. For each, the roots of the resultant `Res_y(P(y), y^d P(xy))` are ratios of eigenvalues, where `P` is the characteristic polynomial. A noncyclotomic irreducible rational factor certifies a ratio that is not a root of unity and hence an infinite *projective* matrix group. Output includes the braid word, characteristic polynomial, resultant and factor for independent checking. The certificate uses exact rational arithmetic, subject to SymPy's exact factorization; it is not a Lean proof.

An inconclusive output, including a node-limit exit, does not establish finiteness. Checking Artin relations alone does not prove that the matrices arise from any category, object, tensor power, or F/R symbols; those links must be established independently. A verified F/R-to-matrix adapter is still needed, as is support for algebraic fields beyond cyclotomic fields. A non-root-of-unity eigenvalue ratio of a braid word is sufficient but not necessary for infinite image; in particular, inspecting generator eigenvalues alone is insufficient. Never infer an exact certificate from floating-point orbit growth.

## Cyclotomic matrices

`cyclotomic_braid.py` accepts matrices over Q(ζₙ), where ζₙ is a primitive n-th root of unity and `order` is n. Each entry is a nonempty list of rational coefficients in increasing powers of ζₙ. For example, a two-strand representation with one diagonal generator is:

```json
{"order": 5, "generators": [[[[0, 1], [0]], [[0], [2]]]]}
```

Run `python3 scripts/propf/cyclotomic_braid.py matrices.json`. The field arithmetic and relation checks are exact. For each word, the tool first forms the ratio resultant over Q(ζₙ), then takes its norm to Q by another resultant with Φₙ. A noncyclotomic irreducible factor of this norm certifies a non-root-of-unity ratio: being a root of unity is preserved by Galois conjugation. The norm may be expensive at large field degrees or matrix dimensions. The same interpretation and inconclusive-result limitations described above apply.

## Literature notes

- Naidu–Rowell, [arXiv:0903.4157](https://arxiv.org/abs/0903.4157), Conjecture 2.3 states the category-level equivalence; Question 4.10 asks whether property F depends only on fusion rules. The two statements are represented separately in Lean.
- Green–Nikshych, [arXiv:1911.02633](https://arxiv.org/abs/1911.02633), Theorem 7.2 proves property F for weakly group-theoretical braided fusion categories. This class is defined by categorical Morita equivalence to a nilpotent category, not by a mere numerical flag.
- Rowell–Wenzl, [arXiv:1401.5329](https://arxiv.org/abs/1401.5329), derive finite Gaussian braid images for the quantum-group cases described there. Gustafson–Rowell–Ruan, [arXiv:1808.00698](https://arxiv.org/abs/1808.00698), establish property F for odd N-metaplectic modular categories; their discussion of even N requires care and does not justify asserting their odd-N result for every even N.
- Galindo–Rowell, [arXiv:1312.5557](https://arxiv.org/abs/1312.5557), study braid images from unitary braided vector spaces and related finite-image questions; a solution for such a vector space is not automatically a braided fusion category realization.
- Li–Ruan, [arXiv:2610.05177](https://arxiv.org/abs/2610.05177), report finite projective mapping-class-group images for weakly group-theoretical modular fusion categories with their canonical positive spherical structures. This generalized property is stronger and different from the braid-image predicate used here.

For results stated using the frozen `PropertyF.Ground` definitions, the identifications with the standard categorical conventions still need the justifications flagged in that interface's module docstring. In particular, a formal statement about the frozen structure should not be silently identified with every categorical or numerical version in the literature.

## Atlas snapshot screen

Run `python3 scripts/propf/atlas_candidates.py > scratch/propf-atlas-candidates.json`. It downloads the manifest and its bosonic `identifiers-exact` and `structure` shards to `scratch/propf-atlas`, verifies each shard against the manifest SHA-256, checks shard IDs and counts, and records the source fingerprint. The manifest itself is not independently authenticated. A cached manifest and cached shards remain fixed between runs; delete the ignored cache to fetch a new snapshot. The script uses the Atlas `weaklyIntegral` and `positiveDimensions` flags, accepts only literal integer exact global dimensions, and reports unflagged literal integers separately. It does not decide general cyclotomic integrality.

For snapshot `4e30d91d46ef0faac774a1e38c6640d6afb604214c44f8c22a81a960c237861a`, the 18,332 bosonic records include 3,410 with the Atlas weak-integral flag, all with literal integer exact global dimensions; 1,089 of these also have positive dimension rows. None of the 1,089 is marked Chern–Simons-ineligible by the Atlas eligibility test. Another 327 records have literal integer categorical global dimension without the weak-integral flag; all have nonpositive dimension rows, so one must not equate their categorical dimensions with FP dimensions.

Of the 1,089 positive-row records, 571 have no realization listed in this export. Of those, 52 have global dimension divisible by at least three distinct primes, so the weakly-group-theoretical theorem for dimensions pᵃqᵇ does not automatically classify them. Their IDs, exact dimensions, Atlas properties, and listed realizations are in the generated JSON. Thirty-eight of those 52 have the Atlas `Prime` tag. Examples include B11-00125, B11-00127, B11-00128, B11-00129, B11-00131, and B11-00134, all with D² = 60. Their dimensions are compatible with odd metaplectic data, so their fusion rules and categorifications require comparison with the known finite-image metaplectic cases before treating them as interesting leads. B18-02036, for example, is listed as a product of B03-00001 and B06-00008; factoring candidates can reveal further known cases.

An empty `realizations` list does not establish that a realization is unknown in the literature, much less that a category is not weakly group-theoretical. Chern–Simons eligibility is not a proof of a realization. Nor does a modular-data record alone establish the pentagon and hexagon solutions needed for property F. At this snapshot the coordination report identifies only B11-00119 as flagged with downloadable F/R symbols, and that entry is not weakly integral. No counterexample is claimed.
