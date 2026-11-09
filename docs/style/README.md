# Pivotal code distribution audit

The [second-pass target dashboard](target-report.md) expands the source census, pins both original and round-two cohorts, and reports the explicit acceptance targets and complete outliers. The historical comparison below retains its original parser for continuity.

The declaration cohort is pinned by fully qualified Lean name at `fb6ec518`, using the then-current survey's module-local, unique terminal-name matches. Current and baseline theorem statistics use only successfully paired declarations; module moves with unchanged public names remain in the cohort. Missing, renamed, private-name changes and newly added or source-unmatched declarations appear in [cohort-unmatched.tsv](cohort-unmatched.tsv); they are not silently counted as improvements. The complete original baseline is [preserved separately](historical-fb6ec518.md).

Proof lines and tactic steps are source-parser heuristics, not elaborated proof size; binder and hypothesis counts come from Lean elaborated types, including section variables. Terminal-name matching is module-local and requires uniqueness. Hypothesis sentinel failures are omitted. Quantiles use linear interpolation. The pinned Mathlib v4.35.0 sample uses SHA-256(module) mod 10 = 0 and is unstratified, not category-theory-specific. Mathlib source and Lean-match counts differ; unmatched source declarations are retained in source metrics only.

| Population | Current files | Source theorems (project paired) | Matched to Lean |
|---|---:|---:|---:|
| New pivotal modules | 164 | 690 | 690 |
| Inherited modules | 130 | 906 | 906 |
| Mathlib sample | 859 | 18060 | 15606 |

## Assessment

For the 690 paired new-layer declarations, source proof-line median/p90 changed 6.0/20.0 → 6.0/17.0; elaborated explicit binders changed 3.0/7.0 → 3.0/6.0. These describe the surviving matched cohort, not the effect of deleted or unpaired declarations.
There are 10 unmatched baseline declarations and 13 unpaired current source declarations. The file distribution is a snapshot of surviving baseline paths, not a paired declaration metric: 14 baseline project paths are absent and 0 current project paths are unclassified. Names are listed below.
Cohort changes require source, consumer, instance, attribute and supported-API review; dependency reachability alone is not a deletion criterion. [Cleanup decisions and retained exceptions](cleanup-notes.md) document the review. The explicit targets for the second pass and their status are reported in the target dashboard.

Among paired new declarations, 408 occur in the current constant-reference dependency union of the six manuscript targets and 282 do not. This is a review aid, not a safe deletion list.

## Distributions

Paired baseline rows use the exact same qualified names as their current rows. The historical tactic-step distribution cannot be paired because the old scorecard did not retain the `by`-proof flag. File counts are not paired.

| Metric | Population | n | p25 | Median | p75 | p90 | p99 | Max |
|---|---|---:|---:|---:|---:|---:|---:|
| Proof lines | New pivotal modules | 690 | 4.0 | 6.0 | 10.0 | 17.0 | 38.11 | 60 |
| Proof lines | Inherited modules | 906 | 2.0 | 3.0 | 9.0 | 12.0 | 26.95 | 48 |
| Proof lines | Mathlib sample | 18060 | 1.0 | 2.0 | 4.0 | 8.0 | 30.0 | 151 |
| Proof lines | New pivotal modules (fb6ec518 paired) | 690 | 4.0 | 6.0 | 12.0 | 20.0 | 43.55 | 63 |
| Proof lines | Inherited modules (fb6ec518 paired) | 906 | 2.0 | 3.0 | 9.0 | 12.0 | 26.95 | 48 |
| Tactic steps (by proofs) | New pivotal modules | 570 | 3.0 | 4.0 | 8.0 | 13.1 | 31.93 | 51 |
| Tactic steps (by proofs) | Inherited modules | 426 | 2.0 | 3.0 | 8.0 | 11.0 | 22.5 | 30 |
| Tactic steps (by proofs) | Mathlib sample | 9295 | 1.0 | 2.0 | 5.0 | 9.0 | 29.0 | 110 |
| Statement characters | New pivotal modules | 690 | 134.0 | 202.5 | 310.0 | 481.0 | 802.77 | 998 |
| Statement characters | Inherited modules | 906 | 112.25 | 153.5 | 222.0 | 278.5 | 413.8 | 565 |
| Statement characters | Mathlib sample | 18060 | 75.0 | 107.0 | 149.0 | 203.0 | 356.0 | 1178 |
| Statement characters | New pivotal modules (fb6ec518 paired) | 690 | 134.0 | 201.5 | 309.0 | 481.0 | 802.77 | 998 |
| Statement characters | Inherited modules (fb6ec518 paired) | 906 | 112.25 | 153.5 | 222.0 | 278.5 | 413.8 | 565 |
| Name characters | New pivotal modules | 690 | 23.0 | 30.0 | 38.0 | 48.0 | 62.11 | 75 |
| Name characters | Inherited modules | 906 | 20.0 | 24.0 | 30.0 | 37.0 | 48.0 | 54 |
| Name characters | Mathlib sample | 18060 | 14.0 | 20.0 | 28.0 | 37.0 | 54.0 | 80 |
| Name characters | New pivotal modules (fb6ec518 paired) | 690 | 23.0 | 30.0 | 38.0 | 48.0 | 62.11 | 75 |
| Name characters | Inherited modules (fb6ec518 paired) | 906 | 20.0 | 24.0 | 30.0 | 37.0 | 48.0 | 54 |
| Explicit binders | New pivotal modules | 690 | 2.0 | 3.0 | 5.0 | 6.0 | 9.0 | 9 |
| Explicit binders | Inherited modules | 906 | 1.0 | 2.0 | 3.0 | 5.0 | 9.0 | 18 |
| Explicit binders | Mathlib sample | 15606 | 1.0 | 2.0 | 2.0 | 4.0 | 6.0 | 15 |
| Explicit binders | New pivotal modules (fb6ec518 paired) | 690 | 2.0 | 3.0 | 5.0 | 7.0 | 9.0 | 11 |
| Explicit binders | Inherited modules (fb6ec518 paired) | 906 | 1.0 | 2.0 | 3.0 | 5.0 | 9.0 | 18 |
| Implicit binders | New pivotal modules | 690 | 0.0 | 1.0 | 1.0 | 3.0 | 6.0 | 8 |
| Implicit binders | Inherited modules | 906 | 1.0 | 2.0 | 3.0 | 5.0 | 7.0 | 11 |
| Implicit binders | Mathlib sample | 15606 | 2.0 | 3.0 | 4.0 | 6.0 | 12.0 | 27 |
| Implicit binders | New pivotal modules (fb6ec518 paired) | 690 | 0.0 | 1.0 | 1.0 | 3.0 | 6.0 | 8 |
| Implicit binders | Inherited modules (fb6ec518 paired) | 906 | 1.0 | 2.0 | 3.0 | 5.0 | 7.0 | 11 |
| Instance binders | New pivotal modules | 690 | 0.0 | 1.0 | 3.0 | 4.0 | 8.0 | 11 |
| Instance binders | Inherited modules | 906 | 0.0 | 2.0 | 4.0 | 7.0 | 11.0 | 15 |
| Instance binders | Mathlib sample | 15606 | 1.0 | 2.0 | 4.0 | 6.0 | 13.0 | 34 |
| Instance binders | New pivotal modules (fb6ec518 paired) | 690 | 0.0 | 1.0 | 3.0 | 4.0 | 8.0 | 11 |
| Instance binders | Inherited modules (fb6ec518 paired) | 906 | 0.0 | 2.0 | 4.0 | 7.0 | 11.0 | 15 |
| Hypotheses | New pivotal modules | 690 | 0.0 | 1.0 | 2.0 | 3.0 | 6.0 | 7 |
| Hypotheses | Inherited modules | 906 | 0.0 | 1.0 | 2.0 | 4.0 | 7.0 | 11 |
| Hypotheses | Mathlib sample | 15606 | 0.0 | 1.0 | 2.0 | 3.0 | 7.0 | 23 |
| Hypotheses | New pivotal modules (fb6ec518 paired) | 690 | 0.0 | 1.0 | 2.0 | 3.0 | 6.0 | 7 |
| Hypotheses | Inherited modules (fb6ec518 paired) | 906 | 0.0 | 1.0 | 2.0 | 4.0 | 7.0 | 11 |
| Elaborated type nodes | New pivotal modules | 690 | 80.0 | 132.5 | 241.5 | 395.5 | 629.17 | 1037 |
| Elaborated type nodes | Inherited modules | 906 | 83.0 | 138.0 | 215.75 | 315.5 | 623.55 | 974 |
| Elaborated type nodes | Mathlib sample | 15606 | 58.0 | 96.0 | 175.0 | 292.0 | 677.0 | 2199 |
| Elaborated type nodes | New pivotal modules (fb6ec518 paired) | 690 | 80.0 | 132.5 | 241.5 | 395.5 | 629.17 | 1037 |
| Elaborated type nodes | Inherited modules (fb6ec518 paired) | 906 | 83.0 | 138.0 | 215.75 | 315.5 | 623.55 | 974 |
| File lines | New pivotal modules | 164 | 49.0 | 70.5 | 106.5 | 155.2 | 420.14 | 439 |
| File lines | Inherited modules | 130 | 84.25 | 145.0 | 198.75 | 265.8 | 534.67 | 894 |
| File lines | Mathlib sample | 859 | 97.5 | 195.0 | 365.5 | 668.8 | 1201.14 | 1503 |
| File lines | Mathlib all files | 8624 | 92.0 | 182.0 | 356.0 | 631.0 | 1239.54 | 1503 |

## Review candidates

These are review priorities, not automatic refactoring requirements. Do not change mathematical statements, hide assumptions, or split proofs into trivial wrappers to fit a distribution.

Longest new proofs:

- `MTC/Center/Normalization/PositiveSubring.lean:18` `pivotalDimension_eq_fp_of_positive_fusionSubring`: 60 lines, 51 estimated tactic steps.
- `MTC/Center/Normalization/IntegerDimensions.lean:48` `pseudoUnitary_of_integer_dimensions_and_center_fp_orthogonality`: 50 lines, 38 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumPrefix.lean:98` `coloredPower_succ_prefix_eq`: 44 lines, 42 estimated tactic steps.
- `MTC/Center/Normalization/PositiveSubring.lean:105` `transparent_norm_saturation_of_adjoint_positivity`: 43 lines, 34 estimated tactic steps.
- `MTC/Braided/Trace/MonodromyReciprocity.lean:39` `norm_inverse_monodromy_trace_eq_of_constituent_phase`: 41 lines, 27 estimated tactic steps.
- `MTC/Braided/Trace/ComplexSaturation.lean:22` `actual_mixed_braid_trace_eq_one_of_saturation`: 40 lines, 29 estimated tactic steps.
- `MTC/Center/Normalization/SymmetricBinomial.lean:131` `canonicalSymmetricPivotal_rising_binomial_isIntegral`: 39 lines, 30 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureColoredFirst.lean:20` `coloredPower_first_mem`: 38 lines, 31 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumInverse.lean:19` `coloredGeneratorInverse_heq_symm`: 38 lines, 25 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureColoredContext.lean:235` `leftTripleCross_word_heq`: 37 lines, 49 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureFlattenConcat.lean:31` `flattenBlocksRecursive_concat_heq`: 37 lines, 27 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureColoredContext.lean:186` `coloredGenerator_zero_flatten_heq`: 34 lines, 24 estimated tactic steps.
- `MTC/PropertyF/Pivotal/NondegeneracyHaarSlide.lean:309` `categoricalHaarRestricted_slide`: 32 lines, 22 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureColoredBridge.lean:52` `coloredGenerator_two_flatten_heq`: 31 lines, 14 estimated tactic steps.
- `MTC/PropertyF/Pivotal/Nondegeneracy.lean:75` `categoricalS_gram_of_unit_character_unique`: 31 lines, 21 estimated tactic steps.
- `MTC/Center/Normalization/SymmetricBinomial.lean:60` `canonicalSymmetricPivotal_falling_binomial_isIntegral`: 30 lines, 23 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureFour.lean:102` `fourBlock_word`: 29 lines, 18 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureJoinAssociativity.lean:17` `joinPowerIso_assoc`: 29 lines, 11 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureInterchange.lean:27` `sweepBlockMerge_succ_prepend`: 28 lines, 10 estimated tactic steps.
- `MTC/PropertyF/Pivotal/MonoidalQuantumTrace.lean:23` `monoidalFunctor_rightQuantumTrace`: 28 lines, 17 estimated tactic steps.

Largest explicit-binder counts among matched new theorems:

- `MTC/Braided/Cabling/PureSumPositiveState.lean:98` `coloredPureWord_cabling_of_positive_states`: 9 explicit, 1 implicit, 4 instance binders.
- `MTC/Braided/Cabling/PureSumPreservation.lean:44` `finite_pureBlock_range_of_colored_group`: 9 explicit, 1 implicit, 3 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:30` `fusionSubring_dualLabel_finrank_zero`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:66` `fusionSubring_dualLabel_finrank_zero_of_supported`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:17` `fusionSubring_forward_finrank_zero`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:48` `fusionSubring_forward_finrank_zero_of_supported`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/PropertyF/Pivotal/NondegeneracyHaarSlide.lean:309` `categoricalHaarRestricted_slide`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/PropertyF/Pivotal/NondegeneracyHaarSlide.lean:413` `doubleBraiding_eq_id_of_restricted_sTest`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/Braided/Cabling/BlockFinite.lean:50` `finite_subgroup_of_finite_preserved_blocks`: 8 explicit, 2 implicit, 3 instance binders.
- `MTC/Braided/Cabling/BlockFinite.lean:95` `finite_braidImage_of_finite_pure_block_ranges`: 8 explicit, 2 implicit, 5 instance binders.
- `MTC/Braided/Cabling/ColorBiproductFinite.lean:22` `finite_pureColor_range_of_cabling`: 8 explicit, 2 implicit, 8 instance binders.
- `MTC/Braided/Cabling/PureSumCabling.lean:53` `coloredPureWord_cabling_of_letters`: 8 explicit, 1 implicit, 4 instance binders.
- `MTC/Braided/Cabling/PureSumColored.lean:410` `pureWord_preserves_coloredBlock`: 8 explicit, 1 implicit, 3 instance binders.
- `MTC/Braided/Cabling/PureSumColored.lean:426` `pureWord_coloredBlock_diagonal`: 8 explicit, 1 implicit, 3 instance binders.
- `MTC/Braided/Cabling/PureSumPositiveState.lean:52` `coloredPowerStateWord_mem_of_positive_letters`: 8 explicit, 1 implicit, 4 instance binders.

## File cohort changes

Absent baseline paths:
- `MTC/Algebra/ComplexTraceReciprocity.lean`
- `MTC/Braided/Cabling/BlockFiniteBraid.lean`
- `MTC/Braided/Cabling/BlockFiniteGroups.lean`
- `MTC/Braided/Cabling/ClosureAdjacentCoherence.lean`
- `MTC/Braided/Cabling/ClosureBlockFinite.lean`
- `MTC/Braided/Cabling/ClosureBlockInduction.lean`
- `MTC/Braided/Cabling/ClosureFlattenUnit.lean`
- `MTC/Braided/Cabling/ClosureFourTail.lean`
- `MTC/Braided/Cabling/ClosureSweepContext.lean`
- `MTC/Braided/Cabling/PureSumPositive.lean`
- `MTC/Braided/Cabling/PureSumPositiveCabling.lean`
- `MTC/Center/Normalization/SymmetricRising.lean`
- `MTC/PropertyF/Pivotal/MonoidalDualComparison.lean`
- `MTC/PropertyF/Pivotal/MonoidalTrace.lean`

Unclassified current paths:
- None.

## Reproduction

`LEAN_NUM_THREADS=4 python3 scripts/style/survey.py` regenerates this report, scorecards and summary statistics. Build the project first. Intermediate elaborated data is git-ignored. `--skip-lean` reuses the existing environment dump and must not be used after changing declarations.
