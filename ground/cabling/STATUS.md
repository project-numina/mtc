# Cabling workstream status

## Done

- `PropertyF.addLeftStrand`, `addLeftStrand_injective`, `strandEmbedding`,
  `strand_inclusion_of_faithful_tensor`: adjoining identity strands gives
  injections of braid images whenever left tensoring is faithful.
- `tensorLeft_faithful_of_unit_retract` and
  `strand_inclusion_of_unit_retract`: a split copy of the unit in `Y ⊗ X`
  implies tensoring by X is faithful and thus gives strand inclusion. Fusion
  and integrate completed the simple-object case as `Ground.simple_strand_inclusion`.

- `strandPermutation`, `pureWords`, `braidWordAction`, `pureBraidImage` and
  `pureBraidImage_finiteIndex`: categorical pure braid images have finite
  index, using permutation of free words.
- `blockRestrictionHom` and `blockRestriction_ker_le` construct and detect
  restrictions of a group action preserving the summands of a finite
  biproduct. `retractActionHom` and `retractAction_ker_le` construct
  restriction to an arbitrary invariant retract. `braidImageRetractMap`
  is a surjective homomorphism between actual braid images for any retract;
  `objectPropertyF_of_retract` establishes the summand transfer.
- `cablingWitnessOfPureAction`: constructs a full `CablingWitness` from
  a pure-word map to the product of cabled braid images and the precise
  kernel containment needed to descend to the pure image.
- `tensorPowerBiproductIso` and `sumPowersTensorPowerIso` construct the
  decomposition of tensor powers of sums of powers into tuple-indexed
  tensor-power blocks. `pureWord_preserves_tupleBlocks` and
  `pureTupleBlockAction_ker_le` reduce pure-word block preservation to
  the generator permutation law. `sumPowersCablingWitness` constructs
  the full witness from that law and membership of pure block restrictions
  in the corresponding X braid images.
- `CablingWitness.of_retract` and `cabling_of_sumPowers` reduce all generated
  objects to proving the cabling diagram only for finite sums of powers.

- `generatedImageEquiv` and `braidImageEquivOfGeneratorCoherence` reduce
  image equivalences under faithful monoidal functors to the generator
  coherence identity. `ker_le_of_mono_intertwiner` proves restriction of
  an action along an invariant summand. Modular subsequently proved full
  braided-functor coherence; `generatedInclusionBraidImageIso` constructs the
  generated inclusion image equivalence unconditionally.

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

- `positiveMatrix_eigenvector_integral` proves the arithmetic/Perron step
  of ENO 8.27: a normalized positive eigenvector of a positive rational
  matrix with rational eigenvalue has integer entries if integral over ℤ.
- `matrix_exists_positive_power` and `connectedMatrix_eigenvector_integral`
  extend this to a nonnegative rational matrix with positive diagonal and
  connected powers, constructing the needed positive power.

## In progress

- Prove the categorical crossing-generator block permutation law and that
  each pure block restriction belongs to its X braid image. These are the
  exact remaining inputs to `sumPowersCablingWitness`.

## Remaining

- Prove `GeneratedBy X (Xᘁ)` from finite semisimplicity and construct
  the fusion structure on the generated subcategory and cabling witnesses.
- Prove the categorical setup for ENO 8.27: the adjoint component, a
  strictly positive power of its fusion matrix, its integer eigenvalue,
  and integrality of coordinates; show inclusion preserves FP dimension.
- The project lacks constructions of fusion categories, semisimplicity, FP
  and FP dimensions. The final target and
  interfaces are being developed by the other workstreams. Full completion
  requires substantial category-theoretic and braid-calculus infrastructure;
  no reliable time estimate is available yet.
