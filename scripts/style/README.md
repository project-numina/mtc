# Style measurement

Run `LEAN_NUM_THREADS=4 python3 scripts/style/survey.py` from the repository.
This imports pinned Mathlib and private project declarations in a separate
analysis module; it does not change the proof library or its dependencies.
Set `PROPERTYF_AUDIT_CORES` to choose the analysis CPU set.

Results are in [docs/style](../../docs/style/README.md). The pinned `docs/style/cohort-fb6ec518.tsv` identifies baseline source
theorems by their uniquely matched Lean names; the report pairs retained
names across moves and records missing or new declarations separately. File
distributions are snapshots, not paired declaration statistics. The Mathlib
sample module list is pinned and checked. The source parser and
Lean expression/binder measurement were adapted from the earlier
`property-f-style/scripts/style` survey without changing their metric
definitions. The source parser is heuristic; the report describes matching
and sampling limitations. File lengths include all Mathlib files as well as
the declaration sample for comparability with the earlier report.

The six dependency roots are the new main theorems, normalization,
pseudo-unitary-conjugate corollary, closure and objectwise theorem.
Constant-reference reachability is not a deletion criterion.

`--skip-lean` is for source/report iteration against an unchanged compiled
environment only. Generated analysis modules and environment TSVs are ignored.
The committed project scorecards and summary support review without checking
in a copy of the Mathlib declaration dataset.

For the target census, run `LEAN_NUM_THREADS=4 python3 scripts/style/survey_proposition_definitions.py`
after the fresh survey, followed by `python3 scripts/style/target_dashboard.py`. It compares the two committed expanded cohorts, lists
all current new-layer source proofs and unpaired identities, records type-hash
changes, and inventories environment-only theorem names. The proposition scan checks proof-valued definitions and opaque declarations
through Lean; the dashboard includes source-matched proofs among them. Generated
name classification is heuristic; the full declaration audit remains the
independent safeguard for private and generated proofs.

The dashboard also reports each target's two interpolation boundary positions,
values and tie counts, plus a fixed-population lower bound on the number of
declarations that would need numerical reductions. This bound allows arbitrary
reductions and says nothing about whether a proposed change is mathematically
valid or improves the API. Middle-length proofs are ranked by file to guide
shared-mathematics review; changes to the population require fresh measurement.
