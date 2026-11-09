# Sustained cleanup target report

**INCOMPLETE:** the proof-length and explicit-binder targets remain missed. Four independently assigned implementation and measurement rounds started from `a93ce31a`. The pinned original `fb6ec518`, round-two `3826bb02`, and sustained-start `a93ce31a` cohorts remain available. Proof lines and tactic steps are source heuristics; binders and hypotheses are measured in Lean. Quantiles use linear interpolation. No impossibility claim follows from the attempts below.

| All current new-layer proofs | Target median / p90 | Achieved median / p90 | Status |
|---|---:|---:|---|
| Source proof lines | ≤3 / ≤12 | 6/17 | **MISSED** |
| Explicit binders | ≤2 / ≤5 | 3/6 | **MISSED** |
| Hypotheses | no worse than 1 / 3 | 1/3 | **MET** |

The current population has 726 proofs and 5,886 proof lines. The 598 tactic-style proofs contain 3,797 estimated steps, median/p90 4/13. Explicit/implicit/strict/instance binder totals are 2537/720/0/1180; total-binder median/p90 is 6/11. All newly extracted helpers are included, including `two_factor_weighted_saturation` in a historically inherited module.

At this fixed population, even allowing arbitrary numerical reductions, at least 178/61 distinct proof reductions are required for the median/p90 targets and 129/39 for explicit binders. These are relaxed lower bounds, not evidence that valid changes exist. The dashboard records boundary positions, values and tie counts.

| Pinned cohort | Paired | Proof lines before → after | Proof median/p90 before → after | Tactic steps before → after | Explicit median/p90 before → after | Hypotheses before → after |
|---|---:|---:|---:|---:|---:|---:|
| `fb6ec518` | 713 | 6,475 → 5,779 | 6/20 → 6/17 | 4,243 → 3,723 (590 → 585 by-proofs) | 3/7 → 3/6 | 1/3 → 1/3 |
| `3826bb02` | 717 | 6,299 → 5,823 | 6/19 → 6/17 | 4,083 → 3,756 (592 → 589 by-proofs) | 3/6 → 3/6 | 1/3 → 1/3 |
| `a93ce31a` | 720 | 6,196 → 5,843 | 6/19 → 6/17 | 4,004 → 3,766 (594 → 592 by-proofs) | 3/6 → 3/6 | 1/3 → 1/3 |

| Area | Start → current proofs | Start → current proof lines | Start → current tactic steps |
|---|---:|---:|---:|
| cabling | 245 → 247 | 2,163 → 2,042 | 1,214 → 1,166 |
| centre | 200 → 200 | 1,672 → 1,577 | 1,214 → 1,134 |
| infrastructure | 133 → 136 | 1,252 → 1,185 | 826 → 767 |
| other new layer | 112 → 113 | 792 → 798 | 542 → 549 |
| trace and algebra | 30 → 30 | 317 → 284 | 208 → 181 |

Unmatched counts (baseline unmatched / current unpaired): original 10/13; round two 0/9; sustained start 0/6. Exact identities and statuses are in the linked inventory.

The [complete current inventory](all-new-proofs.tsv) includes every matched current source proof, including helpers, private proofs, instances and moved results. The [exact outlier inventory](target-outliers.tsv) lists all 133 proofs over 12 lines, 111 declarations above five explicit binders and 50 above three hypotheses, with names, paths and counts. [Unmatched and deleted entries](target-unmatched.tsv) explicitly distinguish each cohort. The [binder-category changes](target-binder-changes.tsv) and [type-hash changes](target-type-hash-changes.tsv) are separate: type hashes do not necessarily expose binder explicitness.

All 717 round-two and 720 sustained-start paired type-expression hashes match. Two original-cohort monoidal duality hashes differ; the earlier pass compared their fully printed types and found them identical. Hashes and textual comparison are evidence, not a semantic equivalence proof.

The accepted public call-convention change makes `pureBlock_range_subset_coloredWords` infer three parameters from its typed maps; its three repository call sites were migrated, and its total binder count and assumptions are unchanged. Four tensor-power phase results moved from `SlopePower` to `SlopeTrace`, with unchanged names and types; the original import path is retained. Other shared additions include actual pure-braid word representation, colored-word intertwining, trace-scalar and monoidal duality naturality, and the general two-factor weighted saturation result. The last has 10 explicit, 5 implicit and 1 instance binder and 7 hypotheses, which are included rather than hidden. Counting the new helper, the rewritten inherited eigenvalue result, and the new-layer tensor-constituent consumer together, proof lines changed from 55 to 35; the inherited proof reduction is not included in the new-layer total.

Independent alternatives were checked rather than assumed impossible. Heterogeneous cabling endpoints require compatible dependent transport; a direct swapped-index and associativity rewrite failed, while a different reassociation simplified part of the proof. A rephased real-weight route for complex saturation checked even with zero weights and zero-dimensional blocks, but its one-use bridge plus application exceeded the existing direct proof. A general weighted induction/adjunction interface did not eliminate the different real and conjugate-pivotal decomposition transports. A proposed delta helper saved no proof cost after another worker used the existing basis-projection API. The more useful two-factor saturation theorem was integrated with two actual consumers. Several opaque simplifier-only or nested-lambda rewrites were rejected to preserve explanatory intermediate facts. The remaining large categorical and arbitrary-subring arguments are review candidates, not proofs of lower bounds.

The matching audit has 0 unmatched current source proofs and 557 environment-only theorem entries; nine are matched inherited source proofs and 548 match generated-name patterns. Generated-name classification is a heuristic; exact names are in [the environment inventory](environment-only-theorems.tsv). The separate [proof-valued definition inventory](proposition-definitions.tsv) checks auxiliaries omitted by theorem-only matching. The kernel audit covers private and generated declarations as well.

Full verification logs and every worker's exact attempts, outliers, changes, and checked handoffs are preserved under `/home/justin_asher/pivotal-cleanup-sustained-20261109-104327`. The final `scripts/check.sh` passed all tests, the full build and the audit of 5,252 declarations; `scripts/audit-target.sh` passed. The fresh explicit public-axiom scan checked 1,678 source proofs, all using only `propext`, `Classical.choice`, and `Quot.sound`. All four frozen hashes matched, the manuscript has no changes from the sustained start, and no conjecture files are tracked. The warning comparison against cached original traces is 197 baseline vs 152 current, with zero missing traces or new/changed diagnostics. Original warning traces are cached evidence, not a fresh baseline rebuild.

Reproduce after building: `LEAN_NUM_THREADS=4 python3 scripts/style/survey.py`, then `LEAN_NUM_THREADS=4 python3 scripts/style/survey_proposition_definitions.py`, then `python3 scripts/style/target_dashboard.py`; `python3 scripts/print_public_axioms.py` checks matched public proofs. The Mathlib 2/8 proof-line and 2/4 explicit-binder references are contextual stretch figures, not acceptance conditions.
