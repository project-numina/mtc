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
