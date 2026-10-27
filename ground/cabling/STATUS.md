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
  constructs its abelian structure from explicit split-mono/epi hypotheses; `Ground.Cabling.generatedCategoryAbelian` now supplies these unconditionally from fusion semisimplicity.
  `generatedCategoryRigidOfDualClosure` constructs rigidity from closure
  under right duals. `generatedBy_dual_of_generator_dual` reduces that
  closure to generation of the generator’s own right dual, and
  `generatedCategoryRigidOfGeneratorDual` constructs rigidity from it.
  `Ground.Cabling.generatedBy_rightDual_of_unit_power` proves that for a
  simple X this membership follows when some positive power contains the
  unit. `Ground.Cabling.unit_retract_power` now constructs that occurrence
  from a balanced fusion flow, and `generatedCategoryRigidOfSimple` constructs
  rigidity without further assumptions for simple generators.
  `Ground.Cabling.generatedBy_rightDual` now uses
  semisimple decomposition and proves dual closure for arbitrary generators;
  `generatedCategoryRigid` constructs their rigidity unconditionally.
  `generatedFusion` bundles this as a genuine braided fusion category;
  `generatedFusionInclusion` is full, faithful and braided, its essential
  image is `GeneratedBy`, and `generatedFusionInclusionBraidImageIso`
  identifies braid images. These constructions use no legacy hypothesis
  structures; their axiom audits show only the three Lean foundations.

- `positiveMatrix_eigenvector_integral` proves the arithmetic/Perron step
  of ENO 8.27: a normalized positive eigenvector of a positive rational
  matrix with rational eigenvalue has integer entries if integral over ℤ.
- `matrix_exists_positive_power` and `connectedMatrix_eigenvector_integral`
  extend this to a nonnegative rational matrix with positive diagonal and
  connected powers, constructing the needed positive power.

## In progress

- `powerSum_crossing_permutesBlocks` proves the categorical crossing-generator
  block permutation law. `moveHead_mem_braidImage` proves a single strand
  crossing an arbitrary block is a braid; `moveHead_spectators` extends this
  to spectator blocks on both sides. The unproved step is the general crossing
  of two tensor-power blocks in arbitrary tuple contexts. Pure-word composition
  is now proved by `powerSum_pureBlock_mem_of_generators`. Empty blocks are
  handled by `blockSwap_zero_left` and `blockSwap_zero_right`; a singleton
  left block is handled by `blockSwap_one_left_mem`. Right insertion works at
  every strand count by `addRightAutAllIter_hom`. The comparison between its
  `concatPowerIso` and the existing tuple normalization remains unproved.
  `objectPropertyF_generated_of_block_membership` proves bundle-free property-F
  transfer conditional on the resulting pure-block membership.

## Remaining

- Construct cabling witnesses using the remaining pure-block cabling identity.
- Fusion completed ENO 8.27 without the adjoint-component construction:
  `Ground.fpSimple_sq_integer_of_weaklyIntegral` and
  `Ground.simple_fpDimension_sq_integer_of_weaklyIntegral` prove simple
  squares integral by a Galois argument. `Ground.Cabling.generated_simple_square_integral`
  connects this result to our bundled generated category and inclusion.
- The general categorical cabling identity remains substantial. No reliable
  completion estimate is available.
