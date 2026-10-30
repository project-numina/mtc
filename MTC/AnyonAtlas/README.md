# Anyon Atlas data

The [Anyon Atlas](https://anyonatlas.org/) is a catalog of modular and
supermodular data. Its [documentation](https://anyonatlas.org/documentation)
defines the notation, properties and realization labels. The paper is Jonah
Berean-Dutcher, Clay Córdova, Julio Parra-Martinez and Richard Tuddenham,
[*The Anyon Atlas*, arXiv:2610.25439](https://arxiv.org/abs/2610.25439).
Cite the paper and the Atlas and give the record ID when using an entry. The
website asks users to cite the Atlas; its suggested BibTeX is:

```bibtex
@misc{berean-dutcher2026anyonatlas,
  author = {Berean-Dutcher, Jonah and C{\'o}rdova, Clay and Parra-Martinez, Julio and Tuddenham, Richard},
  title  = {The Anyon Atlas},
  year   = {2026}
}
```

We did not find a license or redistribution grant for the website's data or
symbol archives. The paper's arXiv license is not a license for the database.
Downloaded and generated copies stay in git-ignored `data/`; confirm terms with
the authors before redistributing them. The committed rank-one Lean sample is
small. All scripts work locally and do not require uploading the data.

## Obtain and generate

Run from the repository root. Python 3 and `curl` are required. The validator
also requires NumPy. The download is resumable and verifies the SHA-256 of every
published source shard against the manifest:

```sh
python3 scripts/atlas/download.py
python3 scripts/atlas/download_symbols.py
python3 scripts/atlas/import.py --output data/generated-small
OPENBLAS_NUM_THREADS=1 python3 scripts/atlas/validate.py
```

The importer requires an empty output directory, to prevent mixing snapshots.
It checks source hashes, schema headers, IDs and joins. It writes a JSON index
and small Lean modules organized by kind, rank, source chunk and part. The
`--max-module-bytes` option sets a target size; a single record is never split,
so a particularly large record can exceed that target. It does not silently
replace previously generated modules. For example, check a generated module:

```sh
LEAN_NUM_THREADS=4 taskset -c 0-3 lake env lean data/generated-small/BosonicRank02Chunk000Part000.lean
```

Adjust the CPU affinity to the cores assigned to your environment. To resolve
the import, first build `MTC.AnyonAtlas.Raw` with Lake. The generated modules are
not part of the default build and are not committed. `MTC/AnyonAtlas/Raw.lean`
represents each exact entry as a sum of rational coefficients times roots of
unity. `MTC/AnyonAtlas/Sample.lean` evaluates the rank-one source record and
connects S and T to the proved `MTC.Modular.Data.trivial`. The general raw
encoding is not yet a constructor for `MTC.Modular.Data`: such a constructor
must supply duals, fusion rules, and proofs of its axioms. In particular, the
fermionic full S matrix is singular and must not be imported as ordinary
modular data. No categorification follows merely from a data record.

The source snapshot retrieved on 2026-10-28 reports 18,332 bosonic and 6,974
fermionic records. Its export fingerprint is
`4e30d91d46ef0faac774a1e38c6640d6afb604214c44f8c22a81a960c237861a`.
The symbol downloader uses the separate live catalog manifest and records its
fingerprint. On that date it advertised F and R archives only for B11-00119;
both hashes were verified. The F archive is about 940 MB. The paper describes
solutions in ranks 11 and 12, but this does not imply the website currently
provides archives for both. Snapshots and coverage may change.

## Queries and interpretation

```sh
python3 scripts/atlas/query.py weakly-integral --index data/generated-small/index.json > data/weakly-integral.json
python3 scripts/atlas/query.py no-known-cs --index data/generated-small/index.json > data/no-known-cs.json
python3 scripts/atlas/query.py not-cs --index data/generated-small/index.json > data/not-cs.json
python3 scripts/atlas/query.py max-dimension --positive-only --index data/generated-small/index.json > data/max-dimension.json
```

Add `--kind bosonic` or `--kind fermionic` as needed. Results are JSON and
include the source fingerprint and record identifiers. The first query uses
the Atlas `weaklyIntegral` flag, not a Lean theorem about a category. The
`not-cs` query follows the catalog display rule: a negative eligibility result
without a known Tannakian extension. `no-known-cs` means no recognizable
Chern–Simons-style realization label in this export; it includes unknown cases
and does not establish nonrealizability. Both queries depend on the Atlas
classification and its conventions; inspect the raw realization fields and
catalog before making claims. The export and live catalog have independently
versioned fingerprints.

The maximum query evaluates the exact dimension expressions numerically and
returns one approximate maximizer per kind and rank, so ties and close values
need exact verification. `--positive-only` selects the Atlas positive-dimension
flag; positive dimensions are necessary for unitarity, not a proof of it. It
also avoids treating a non-pseudo-unitary categorical dimension as the
Frobenius–Perron dimension. The index preserves the source's exact formatted
global dimension and central charge, diagonal twist order, integrality flag,
and realization metadata. `cyclotomicFieldOrderUpperBound` is the least common
multiple of the denominators appearing in the exact S and T expressions; it
specifies a containing cyclotomic field, not necessarily the minimal conductor.
The dimension-field conductor, when reported by the Atlas, is retained inside
`chernSimonsEligibility` and is a different invariant.

Use these queries to generate candidate patterns and then prove them against
precise definitions. Separate an observed finite range from a universal claim,
and distinguish data, categorification, and category-level property F. In
particular, the existence of modular data does not imply the existence of F and
R symbols, and no weakly integral record is thereby known to have property F.

## Validation scope

The validator checks hashes and cross-family IDs and evaluates expressions with
floating-point complex arithmetic. It checks shape, symmetry, vacuum row,
twists and sparse fusion representation; for bosonic records it additionally
checks scaled unitarity, charge conjugation, the modular relation and fusion
diagonalization. It does not test every possible consistency condition, verify
the pentagon or hexagon equations, or provide exact proofs. Fermionic entries
receive only checks appropriate to their full degenerate S matrix. The JSON
report lists every flagged ID and check; a failure may be rounding or an
incorrect assumption in the checker rather than an error in the Atlas. Passing
is evidence, not a certificate. For exact Lean proofs start with the rank-one
sample and extend the shared mathematical interface and finite computations.
