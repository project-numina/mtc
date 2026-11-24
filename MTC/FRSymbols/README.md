# F and R symbols

The Lean modules define fusion multiplicities, matrix-valued F and R symbols,
gauge transformations, coherence equations, and exact cyclotomic coefficients.
The pointed and toric-code examples contain checked finite calculations.
These interfaces do not by themselves establish full category reconstruction.

## Verify an exact F-table

From the repository root, with Python 3 and the pinned Lean toolchain on your
path, run

```sh
python3 scripts/verify_pentagon.py MTC/FRSymbols/Ising.json --proof IsingPentagon.lean
lake env lean IsingPentagon.lean
```

The first command builds the required Lean module, checks the table, and saves
a replayable theorem. The second rechecks that theorem on the same checkout.
Omitting `--proof` performs the same check and prints the source digest. On a
pentagon failure the verifier reports the external labels, intermediate
channels, and six trivalent vertex indices of a failing equation.

The theorem `all_pentagons : table.Pentagon` lives in a namespace keyed by the input digest. It proves the fusion-rule laws and
the pentagon for every admissible pair of fusion trees over the stated
cyclotomic field. It uses the same equation as `MatrixSymbols.Pentagon`.
Invertibility of the associators, unitarity, braiding and identification with
modular data are separate claims.

### Submit a table for pentagon verification

The candidate file can live anywhere on the agent's machine. From the
repository root, verify it locally by giving the command a new output directory.

```sh
python3 scripts/submit_f_symbols.py /path/to/candidate.json --local /tmp/verified-table
```

Once the workflow is installed on `main`, an agent with an authenticated
GitHub CLI and Actions write permission on the repository can dispatch it.
The command prints the run URL. The inline submission limit is 48,000 bytes.

```sh
python3 scripts/submit_f_symbols.py /path/to/candidate.json --repo project-numina/mtc
```

On success, the run saves a **pentagon verified** artifact. It contains the
original file as `input.json`, the kernel-checked theorem as `Proof.lean`,
and a `manifest.json` recording the claim, input SHA-256 and verifier commit.
Local mode writes the same artifact files. A failing pentagon is reported with
its indices in the verification log. The workflow ends at artifact creation.

To replay a downloaded bundle, set `BUNDLE` to its absolute path and run
these commands from a checkout at the manifest's `verifier_commit`.

```sh
(cd "$BUNDLE" && jq -r '.input_sha256 + "  input.json"' manifest.json | sha256sum --check)
lake build MTC.FRSymbols.PentagonTable
lake env lean "$BUNDLE/Proof.lean"
```

### Ising and Anyon Atlas record IDs

For a rank-three submission the verifier also compares its fusion tensor to
the 24 bosonic records in the bundled [Anyon Atlas fusion pack](https://anyonatlas.org/data-v2-compact/p-a9cbe6689c07383d/catalog/bosonic/fusion-packs/03/00000.json.gz).
The source fingerprint and SHA-256 pin the catalog data. The reader expands
the upper-triangular products in Atlas order and tries each simple-label
permutation. For every reported match, Lean checks that the permutation is
bijective and preserves the unit, duality, and all 27 fusion multiplicities.
As with the F-table proof, translation of the source bytes to Lean literals
uses a Python reader. The bundle includes the exact compressed pack.

Run the example and inspect the label maps with:

```sh
python3 scripts/submit_f_symbols.py MTC/FRSymbols/Ising.json --atlas-target B03-00019 --local /tmp/ising-atlas
jq '.atlas_fusion.matches[] | [.record_id, .submission_to_atlas]' /tmp/ising-atlas/manifest.json
lake env lean /tmp/ising-atlas/AtlasFusion.lean
```

The Ising input matches the fusion rules of `B03-00008` through `B03-00023`.
For the conventional positive-dimension Ising theory with σ twist
exp(πi/8), the catalog target is `B03-00019`. Its order is (unit, ψ, σ),
so the candidate-to-Atlas map is `[0, 2, 1]`.
The dimension and twist specify the intended target externally. The formal
link for that ID certifies fusion-rule agreement. [Pinned Atlas dimensions and twists](https://anyonatlas.org/data-v2-compact/p-a9cbe6689c07383d/catalog/bosonic/ranks/03/000.json)

The optional `--atlas-target` is recorded as the submitter's `proposed_target`
even if the snapshot has no matching record. The version 1 manifest lists each verified claim type, proof filename and
proof checksum under `verifications`. The `atlas_fusion` field records the
catalog snapshot, label maps, and fully qualified Lean theorem names.
An empty match list means the snapshot was searched. The field is omitted
for ranks outside this snapshot.

### JSON format, version 1

[The Ising table](Ising.json) is a complete example.
It uses labels in the order unit, σ, ψ and the gauge of Rowell, Stong and Wang.
The nontrivial two-channel block has entries ±1/√2, encoded using
1/√2 = (ζ₈ − ζ₈³)/2. [Published Ising data, §5.3.4](https://arxiv.org/pdf/0712.1377#page=37)

| Field | Meaning |
| --- | --- |
| `version` | The integer 1. |
| `order` | Positive integer n specifying the coefficient field ℚ(ζₙ) and its standard primitive root. |
| `unit`, `dual` | Zero-based label of the tensor unit and an array giving the dual of each label. The array length is the rank. |
| `fusion` | Dense array of nonnegative integers. Entry `fusion[a][b][c]` is the multiplicity of c in a ⊗ b. |
| `strict_unit` | When true, any block with a unit among a, b, c is the identity in the specified row and column order. These blocks may be omitted. |
| `blocks` | An array of objects with `labels` equal to [a,b,c,d] and `rows` holding the matrix of $F^{abc}_d$. Supply every nonempty block except implicit identities. |

For a block, enumerate rows as (e,α,β), with α indexing a ⊗ b → e and β
indexing e ⊗ c → d. Enumerate columns as (g,δ,ε), with δ indexing b ⊗ c → g
and ε indexing a ⊗ g → d. Both orders are lexicographic, starting at zero.
Every scalar is an array of at most φ(n) rational coefficients in increasing
powers of ζₙ. Use JSON integers or quoted fractions with a positive
denominator. Trailing zeros may be dropped, so `[]` is zero and `[1]` is one.

### What Lean checks

The Python reader translates JSON into the literal Lean table included in the
proof file, including the expansion of implicit unit blocks. The kernel checks
its dimensions, fusion laws, the polynomial relation used for exact arithmetic,
and the two contractions for every pair of trees. The JSON reader is part of
the trust boundary for associating that theorem with an input file. The SHA-256
in the proof records which bytes were read. Regenerating the proof from the
submitted file checks that association through the same reader.
