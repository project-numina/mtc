# F and R symbols

`FusionRules.lean` defines finite fusion multiplicities. `MatrixSymbols.lean`
contains matrix-valued F and R blocks, their inverses, the pentagon, both
hexagons, and unitarity relative to a complex embedding. `MatrixGauge.lean`
describes changes of trivalent bases. `Metric.lean` defines compatible positive
Hermitian fusion-space metrics for nonorthonormal bases and requires F and R
to preserve the induced tree metrics. These coherence equations are not yet a
complete category reconstruction: triangle, rigidity, pivotal/ribbon
structure and category-level comparison remain to be implemented.

`Pointed.lean` specializes the equations to pointed categories. `ToricCode.lean`
proves the pointed pentagon, hexagons, and unitarity for the toric code.
`ToricMatrix.lean` separately proves both full matrix hexagons, block
invertibility and unitarity, and matches its R blocks to the pointed data.
Its general matrix pentagon is not yet proved. `ToricModularData.lean`
constructs the associated exact unnormalized S, twist and fusion data.

`Cyclotomic.lean` represents exact coefficients in `ℚ[X]/(Φₙ)` and provides
the standard complex embedding and an equality criterion using remainders.
For positive `n`, the quotient has a field instance and the class of `X` is
proved to be a primitive `n`th root. Exact conjugation sends it to its
inverse, and the standard complex embedding preserves this involution.
`CyclotomicMatrix.lean` proves that exact matrix unitarity is equivalent to
unitarity after complex embedding.

## Local Atlas symbol blocks

The Atlas catalog snapshot downloaded on 2026-10-28 provides F and R archives
for B11-00119. The 940 MB F archive and the R archive are downloaded and
checksum verified by `scripts/atlas/download_symbols.py`. They use power-basis
coefficients in `ℚ(ζ₇₀)` and the same lexicographic fusion-tree order as the
matrix interface. The F archive omits strict-unit blocks; restoring them is a
separate step. The published rank-12 solution was not available as a symbol
archive in this snapshot.

After downloading and unpacking an archive locally, emit one block as Lean:

```sh
python3 MTC/FRSymbols/import_atlas_block.py \
  data/symbols/B11-00119-R-symbols/rsymbols.aasym 1 1 0 \
  --output data/generated-r110.lean \
  --certificate MTC/FRSymbols/B11R110Certificate.lean.txt
LEAN_NUM_THREADS=4 taskset -c 12-15 lake env lean data/generated-r110.lean
```

For F, supply four labels in the order `(a,b,c,d)`; for R, supply three in the
order `(a,b,c)`. The generated declarations preserve the source matrix
ordering and namespace blocks by kind, rank, and labels. Values are emitted as
rational polynomials in the quotient generator, without floating-point
conversion. This is a block importer, not a whole-solution verifier: it does
not assemble fusion rules, reconstruct omitted blocks, prove matrix
invertibility or unitarity, check coherence, or match modular data. It expects
an already verified and unpacked payload and does not check the catalog hash.
The optional certificate checks that this specific imported R entry equals
`ζ₇₀⁶⁴` and has complex norm one; it does not certify the other blocks.
To check the downloaded R blocks independently with exact integer polynomial
arithmetic (SymPy is used only to construct `Φₙ`), run:

```sh
python3 MTC/FRSymbols/check_atlas_r.py data/symbols/B11-00119-R-symbols/rsymbols.aasym
```

The downloaded snapshot has 917 R blocks; all pass this exact Python check.
Four 2×2 blocks and one 4×4 block were also checked by independent SymPy
polynomial reduction, with deliberately corrupted entries rejected. The
Python computation is not a Lean proof, and it does not verify that every
required block is present or establish F/R coherence.

The first five supplied F blocks fail ordinary matrix unitarity in their
archived basis. For the first block, the exact first-row norm-squared reduction
was independently checked with SymPy. This does not contradict the paper's
unitary categorification: the basis may require a compatible inner product or
a gauge change. Reproduce the bounded check with:

```sh
python3 MTC/FRSymbols/check_atlas_f.py data/symbols/B11-00119-F-symbols/fsymbols.aasym
```

Generated data remain under ignored `data/` pending redistribution terms.
