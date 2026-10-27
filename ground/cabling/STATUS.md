# Cabling workstream status

## Done

- `PropertyF.addLeftStrand`, `addLeftStrand_injective`, `strandEmbedding`,
  `strand_inclusion_of_faithful_tensor`: adjoining identity strands gives
  injections of braid images whenever left tensoring is faithful.
- `tensorLeft_faithful_of_unit_retract` and
  `strand_inclusion_of_unit_retract`: a split copy of the unit in `Y ⊗ X`
  implies tensoring by X is faithful and thus gives strand inclusion.

- `strandPermutation`, `pureWords`, `braidWordAction`, `pureBraidImage` and
  `pureBraidImage_finiteIndex`: categorical pure braid images have finite
  index, using permutation of free words.
- `cablingWitnessOfPureAction`: constructs a full `CablingWitness` from
  a pure-word map to the product of cabled braid images and the precise
  kernel containment needed to descend to the pure image.

- `generatedImageEquiv` and `braidImageEquivOfGeneratorCoherence` reduce
  image equivalences under faithful monoidal functors to the generator
  coherence identity. `ker_le_of_mono_intertwiner` proves restriction of
  an action along an invariant summand.

- `generatedCategory` and `generatedInclusion` give the full subcategory
  and inclusion; `generatedInclusion_essentialImage` characterizes its
  essential image. `generatedBy_tensorPower`, `generatedBy_unit`,
  `generatedBy_self`, `generatedBy_retract`, `generatedBy_of_iso` establish
  basic closure. `generatedBy_finiteBiproduct`, `generatedBy_finiteProducts`,
  `generatedBy_containsZero` give finite sums, finite products and zero.
  `tensorPowerTensorIso` combines two powers using the
  monoidal associator. `generatedBy_tensor` and `generatedBy_isMonoidal`
  construct tensor closure and the inherited braided monoidal structure,
  with braided full faithful inclusion. `generatedCategoryAbelianOfSplit`
  constructs its abelian structure from explicit split-mono/epi hypotheses.
  `generatedCategoryRigidOfDualClosure` constructs rigidity from closure
  under right duals. `generatedBy_dual_of_generator_dual` reduces that
  closure to generation of the generator’s own right dual, and
  `generatedCategoryRigidOfGeneratorDual` constructs rigidity from it.
  Establishing that one membership and the fusion structure remains.

## In progress

- Obtain the split unit for simple X from rigidity, semisimplicity, and the
  simple unit. Fusion has been asked for the corresponding construction.
- Construct the categorical pure-word map to cabled images and prove its
  kernel containment for a retract of a sum of powers.
- Prove the generator coherence identity for braided functors, so the
  image-equivalence construction applies without an extra hypothesis.

## Remaining

- Prove `GeneratedBy X (Xᘁ)` from finite semisimplicity and construct
  the fusion structure on the generated subcategory,
  its braid image equivalence, and cabling witnesses.
- Prove ENO 8.27 and preservation of FP dimension along the inclusion.
- The project lacks constructions of fusion categories, semisimplicity, FP
  dimensions and nonzero-object tensor faithfulness. The final target and
  interfaces are being developed by the other workstreams. Full completion
  requires substantial category-theoretic and braid-calculus infrastructure;
  no reliable time estimate is available yet.
