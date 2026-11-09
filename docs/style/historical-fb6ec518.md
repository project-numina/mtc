# Pivotal code distribution audit

Survey baseline: original completed pivotal proof, `9c2484eb`; new modules are those added or modified since `56dd74cd`. Current working tree is measured. Historical methodology: `property-f-style/scripts/style/survey.py`, copied into this repository as `source_metrics.py`. Lean/Mathlib v4.35.0.

Source parsing and tactic counts are lexical estimates; binders and hypotheses come from Lean's elaborated types, including section variables. Only unique module-local terminal-name matches are retained. Hypothesis sentinel failures are omitted. Quantiles use linear interpolation. The Mathlib sample is the same deterministic SHA-256(module) mod 10 = 0 sample as the previous survey; it is unstratified and is not a category-theory-only benchmark. New-module statistics include helper declarations, not just the final theorem.

| Population | Files | Source theorems | Matched to Lean |
|---|---:|---:|---:|
| New pivotal modules | 178 | 700 | 700 |
| Inherited modules | 130 | 906 | 906 |
| Mathlib sample | 859 | 18060 | 15606 |

## Assessment

The new proof layer is longer and more fragmented than the inherited cleaned library: proof-line median/p90 are 6/20 versus 3/12; explicit-binder median/p90 are 3/7 versus 2/5; file-line median is 67 versus 145. These are descriptive differences, not a statistical test or evidence of incorrectness.
Hypothesis median/p90 (1/3) matches the Mathlib sample, so a blanket reduction in assumptions is not indicated. Prioritize coherent consolidation of the many small cabling, trace and reduction modules, then review the longest proofs for mathematical reuse and explicit parameters that Lean can infer naturally.
Keep the final theorem entry points short and readable. Any future refactoring must preserve exact statements, complete library builds, the statement-equivalence check and the axiom audits. Matching Mathlib quantiles is not itself a completion criterion.

Of 700 matched new source theorems, 406 occur in the constant-reference dependency union of the six manuscript targets and 294 do not. The latter are review candidates, not safe automatic deletions: elaboration, attributes, instances and reusable public APIs require separate inspection.

The old October 27 survey had proof-line median/p90 8/26 and 509 files before the earlier cleanup. The relevant regression comparison here is the current inherited library, not that pre-cleanup snapshot.

## Distributions

| Metric | Population | n | p25 | Median | p75 | p90 | p99 | Max |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| Proof lines | New pivotal modules | 700 | 4.0 | 6.0 | 11.25 | 20.0 | 43.05 | 63 |
| Proof lines | Inherited modules | 906 | 2.0 | 3.0 | 9.0 | 12.0 | 26.95 | 48 |
| Proof lines | Mathlib sample | 18060 | 1.0 | 2.0 | 4.0 | 8.0 | 30.0 | 151 |
| Tactic steps (by proofs) | New pivotal modules | 585 | 3.0 | 5.0 | 9.0 | 16.0 | 34.8 | 55 |
| Tactic steps (by proofs) | Inherited modules | 426 | 2.0 | 3.0 | 8.0 | 11.0 | 22.5 | 30 |
| Tactic steps (by proofs) | Mathlib sample | 9295 | 1.0 | 2.0 | 5.0 | 9.0 | 29.0 | 110 |
| Statement characters | New pivotal modules | 700 | 135.75 | 203.0 | 309.0 | 481.0 | 802.07 | 998 |
| Statement characters | Inherited modules | 906 | 112.25 | 153.5 | 222.0 | 278.5 | 413.8 | 565 |
| Statement characters | Mathlib sample | 18060 | 75.0 | 107.0 | 149.0 | 203.0 | 356.0 | 1178 |
| Name characters | New pivotal modules | 700 | 23.0 | 30.0 | 38.0 | 47.1 | 62.01 | 75 |
| Name characters | Inherited modules | 906 | 20.0 | 24.0 | 30.0 | 37.0 | 48.0 | 54 |
| Name characters | Mathlib sample | 18060 | 14.0 | 20.0 | 28.0 | 37.0 | 54.0 | 80 |
| Explicit binders | New pivotal modules | 700 | 2.0 | 3.0 | 5.0 | 7.0 | 9.0 | 11 |
| Explicit binders | Inherited modules | 906 | 1.0 | 2.0 | 3.0 | 5.0 | 9.0 | 18 |
| Explicit binders | Mathlib sample | 15606 | 1.0 | 2.0 | 2.0 | 4.0 | 6.0 | 15 |
| Implicit binders | New pivotal modules | 700 | 0.0 | 1.0 | 1.0 | 3.0 | 6.0 | 8 |
| Implicit binders | Inherited modules | 906 | 1.0 | 2.0 | 3.0 | 5.0 | 7.0 | 11 |
| Implicit binders | Mathlib sample | 15606 | 2.0 | 3.0 | 4.0 | 6.0 | 12.0 | 27 |
| Instance binders | New pivotal modules | 700 | 0.0 | 1.0 | 3.0 | 4.0 | 8.0 | 11 |
| Instance binders | Inherited modules | 906 | 0.0 | 2.0 | 4.0 | 7.0 | 11.0 | 15 |
| Instance binders | Mathlib sample | 15606 | 1.0 | 2.0 | 4.0 | 6.0 | 13.0 | 34 |
| Hypotheses | New pivotal modules | 700 | 0.0 | 1.0 | 2.0 | 3.0 | 6.0 | 7 |
| Hypotheses | Inherited modules | 906 | 0.0 | 1.0 | 2.0 | 4.0 | 7.0 | 11 |
| Hypotheses | Mathlib sample | 15606 | 0.0 | 1.0 | 2.0 | 3.0 | 7.0 | 23 |
| Elaborated type nodes | New pivotal modules | 700 | 80.0 | 133.0 | 242.0 | 393.2 | 624.47 | 1037 |
| Elaborated type nodes | Inherited modules | 906 | 83.0 | 138.0 | 215.75 | 315.5 | 623.55 | 974 |
| Elaborated type nodes | Mathlib sample | 15606 | 58.0 | 96.0 | 175.0 | 292.0 | 677.0 | 2199 |
| File lines | New pivotal modules | 178 | 46.25 | 67.0 | 100.75 | 149.0 | 448.75 | 535 |
| File lines | Inherited modules | 130 | 84.25 | 145.0 | 198.75 | 265.8 | 534.67 | 894 |
| File lines | Mathlib sample | 859 | 97.5 | 195.0 | 365.5 | 668.8 | 1201.14 | 1503 |
| File lines | Mathlib all files | 8624 | 92.0 | 182.0 | 356.0 | 631.0 | 1239.54 | 1503 |

## Review candidates

These are review priorities, not automatic refactoring requirements. Do not change mathematical statements, hide assumptions, or split proofs into trivial wrappers to fit a distribution.

Longest new proofs:

- `MTC/Center/Normalization/PositiveSubring.lean:18` `pivotalDimension_eq_fp_of_positive_fusionSubring`: 63 lines, 55 estimated tactic steps.
- `MTC/Center/Normalization/IntegerDimensions.lean:48` `pseudoUnitary_of_integer_dimensions_and_center_fp_orthogonality`: 54 lines, 39 estimated tactic steps.
- `MTC/Braided/Trace/MonodromyReciprocity.lean:45` `norm_inverse_monodromy_trace_eq_of_constituent_phase`: 52 lines, 39 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumPrefix.lean:98` `coloredPower_succ_prefix_eq`: 51 lines, 50 estimated tactic steps.
- `MTC/Center/Induction/PivotalSquare.lean:40` `globalDimension_square_of_actual_induction`: 49 lines, 33 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureColoredContext.lean:194` `coloredGenerator_zero_flatten_heq`: 48 lines, 24 estimated tactic steps.
- `MTC/Braided/Trace/ComplexSaturation.lean:22` `actual_mixed_braid_trace_eq_one_of_saturation`: 48 lines, 33 estimated tactic steps.
- `MTC/Center/Normalization/PositiveSubring.lean:108` `transparent_norm_saturation_of_adjoint_positivity`: 43 lines, 34 estimated tactic steps.
- `MTC/Center/Normalization/ScalarFusionCharacter.lean:69` `dimensionRatio_tensor_constituent`: 43 lines, 34 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumPrefix.lean:167` `coloredPower_positive_mem`: 39 lines, 29 estimated tactic steps.
- `MTC/Center/Normalization/SymmetricRising.lean:58` `canonicalSymmetricPivotal_rising_binomial_isIntegral`: 39 lines, 30 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureColoredFirst.lean:20` `coloredPower_first_mem`: 38 lines, 31 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumInverse.lean:19` `coloredGeneratorInverse_heq_symm`: 38 lines, 25 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureColoredContext.lean:284` `leftTripleCross_word_heq`: 37 lines, 49 estimated tactic steps.
- `MTC/Braided/Cabling/ClosureFlattenConcat.lean:31` `flattenBlocksRecursive_concat_heq`: 37 lines, 27 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumPositiveState.lean:72` `coloredPureWord_cabling_of_positive_states`: 36 lines, 25 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumCabling.lean:13` `coloredPureWord_cabling_of_letters`: 34 lines, 25 estimated tactic steps.
- `MTC/PropertyF/Pivotal/MonoidalQuantumTrace.lean:56` `monoidalFunctor_leftQuantumTrace`: 34 lines, 24 estimated tactic steps.
- `MTC/Braided/Cabling/PureSumSigned.lean:22` `coloredPower_negative_eq_inverse`: 33 lines, 25 estimated tactic steps.
- `MTC/PropertyF/Pivotal/FPObject.lean:33` `existsUnique_fp_column`: 33 lines, 24 estimated tactic steps.

Largest explicit-binder counts among matched new theorems:

- `MTC/Braided/Cabling/PureSumPreservation.lean:57` `finite_pureBlock_range_of_cabling`: 11 explicit, 1 implicit, 3 instance binders.
- `MTC/Algebra/ComplexBraidSaturation.lean:16` `braid_squares_equal_on_support`: 10 explicit, 0 implicit, 0 instance binders.
- `MTC/Braided/Cabling/BlockFinite.lean:15` `finite_type_of_finite_preserved_blocks`: 10 explicit, 2 implicit, 3 instance binders.
- `MTC/Braided/Cabling/ClosureColoredContext.lean:117` `firstCross_suffix_cancel`: 9 explicit, 1 implicit, 3 instance binders.
- `MTC/Braided/Cabling/ColorBiproductConstant.lean:44` `finite_pureBlock_range_of_equal_colors`: 9 explicit, 1 implicit, 6 instance binders.
- `MTC/Braided/Cabling/PureSumPositiveState.lean:72` `coloredPureWord_cabling_of_positive_states`: 9 explicit, 1 implicit, 4 instance binders.
- `MTC/Braided/Cabling/PureSumPreservation.lean:30` `finite_pureBlock_range_of_colored_group`: 9 explicit, 1 implicit, 3 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:18` `fusionSubring_dualLabel_finrank_zero`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:41` `fusionSubring_dualLabel_finrank_zero_of_supported`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:65` `fusionSubring_forward_finrank_zero`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/Center/Normalization/FusionSubringSupport.lean:77` `fusionSubring_forward_finrank_zero_of_supported`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/PropertyF/Pivotal/NondegeneracyHaarSlide.lean:84` `haarRotatedBlock_eq_partialTrace`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/PropertyF/Pivotal/NondegeneracyHaarSlide.lean:185` `haarRotatedBlock_comp`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/PropertyF/Pivotal/NondegeneracyHaarSlide.lean:345` `categoricalHaarRestricted_slide`: 9 explicit, 0 implicit, 0 instance binders.
- `MTC/PropertyF/Pivotal/NondegeneracyHaarSlide.lean:514` `doubleBraiding_eq_id_of_restricted_sTest`: 9 explicit, 0 implicit, 0 instance binders.

## Reproduction

`LEAN_NUM_THREADS=4 python3 scripts/style/survey.py` regenerates this report, project source scorecards and summary statistics. Intermediate elaborated data is git-ignored. `--skip-lean` reuses the existing environment dump and must not be used after changing declarations.
