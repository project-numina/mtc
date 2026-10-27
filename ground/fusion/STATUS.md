# Fusion workstream status

## Done

- `FusionData.finrank_simple_hom`: Schur's lemma gives the Kronecker-delta
  Hom dimensions of the existing simple representatives.
- `FusionData.simple_endomorphism_scalar`: endomorphisms of each representative
  are complex scalars.
- `FusionData.fpDimension_simple`: the existing object FP-dimension expression
  agrees with the specified character on each representative.
- `FusionData.fpSimple_isIntegral`, `fpDimension_isIntegral`, and
  `globalFPDimension_isIntegral`: the fusion equations give an integer matrix
  having the positive character as eigenvector, so its values and their finite
  sums and products are algebraic integers.
- `Ground.integer_matrix_eigenvalue_isIntegral`: a reusable matrix theorem
  with no dependency on the old fusion or numerical hypothesis structures.
- `Ground.integer_matrix_spectralRadius_sq_isIntegral`,
  `Ground.fpSimple_isIntegral`, and `Ground.globalFPDimension_isIntegral`:
  the target's spectral-radius simple dimensions and global dimension are
  algebraic integers, without assuming a positive character or old bundles.
- `Ground.fusionMatrix_unit`, `Ground.fpSimple_unit`, and
  `Ground.one_le_globalFPDimension`: the spectral-radius definition is
  normalized at the unit and the global dimension is at least one.
- `Ground.split_to_simple`, `simple_projective`, `simple_injective`,
  `object_projective`, `object_injective`, `epi_splits`, and `mono_splits`:
  every object is projective and injective, and all epimorphisms and
  monomorphisms split.
- `Ground.split_from_simple`: any nonzero map out of a simple object splits,
  using the genuine finite semisimplicity property.
- `Ground.unit_retract_leftDual_tensor`: the tensor unit is a retract of
  `ᘁX ⊗ X` for simple `X`, supplying the cabling strand-inclusion input.
- `Ground.simples_simple`, `simples_injective`, `simples_decompose`,
  `exists_simple_iso`, `exists_unit_iso`, and `finrank_simples_hom`: the
  target's representatives enumerate all simple objects, including the unit,
  and satisfy Schur's Hom formula without using old fusion structures.
- `Ground.homBiproductLinearEquiv`, `finrank_hom_biproduct`,
  `finrank_simple_of_decomposition`, `exists_canonical_decomposition`:
  Hom-space dimensions compute decomposition multiplicities, and every object
  decomposes with those canonical multiplicities.
- `Ground.tensor_multiplicity`, `fusionCoeff_unit`, `fusionCoeff_comm`, and
  `fusionCoeff_assoc`: tensor product acts on multiplicities through the actual
  fusion coefficients, which satisfy the unit, commutativity and associativity
  laws for the genuine target category.
- `Ground.tensorRightHomLinearEquiv`, `finrank_frobenius_reciprocity`, and
  `fusionCoeff_reciprocity`: rigidity gives complex-linear Hom equivalences and
  Frobenius reciprocity with the actual left dual object.
- `Ground.finrank_end_leftDual`, `simple_of_finrank_end_eq_one`,
  `simple_leftDual`, `dualIndex`, `dualIndex_involutive`, `dualEquiv`, and
  `fusionCoeff_reciprocity_labels`: the actual dual of each simple is simple,
  duality gives an involutive permutation of labels, and the usual
  Frobenius reciprocity identity follows.
- `Ground.totalFusionMatrix_symmetric` and `totalFusionMatrix_pos`: the sum of
  the real fusion matrices is symmetric and strictly positive. Positivity uses
  cabling's `tensorLeft_faithful_of_unit_retract` (merged commit 288c894).
- `Ground.positive_matrix_eigenspace_unique`: any eigenspace containing a
  strictly positive eigenvector of a positive real matrix is one-dimensional.
- `Ground.positive_symmetric_matrix_has_positive_eigenvector`: every strictly
  positive symmetric real matrix has a strictly positive eigenvector, proved by
  maximizing its quadratic form on a sphere and applying Mathlib's symmetric
  operator spectral theory.
- `Ground.characterMatrix_commute`, `exists_positive_common_eigenvector`, and
  `exists_positive_character`: the actual fusion rules admit a positive
  normalized character, constructed from the genuine target category.
- `Ground.positive_character_unique`, `fpCharacter`, `fpCharacter_pos`,
  `fpCharacter_unit`, and `fpCharacter_mul`: that character is unique and is
  available as a constructed function with its fundamental laws.
- `Ground.fpSimple_eq_fpCharacter`, `fpSimple_pos`, and `fpSimple_mul`: the
  target's spectral-radius dimensions are exactly that positive character.
  This uses `Dimensions.character_norm_le_fpSimple` from dimensions commit
  e5a83b8 and `complex_eigenvalue_le_positive_eigenvalue` for the reverse bound.
- `Ground.fusionMatrix_dual`, `fpSimple_dual`, and `one_le_fpSimple`: simple
  FP dimensions are invariant under duals and at least one.
- `Ground.fusionData`, `fusionData_globalFPDimension`: every field of the
  earlier `FusionData` is constructed from the genuine target category; this
  compatibility bridge is separate from the strict target dependency cone.
- `Ground.fpDimension` and its `simple`, `iso`, `unit`, `nonneg`, `isIntegral`,
  and `tensor` theorems, plus `one_le_fpDimension`: object FP dimension is
  constructed from Hom multiplicities, tensor-multiplicative, integral over ℤ,
  and at least one on nonzero objects.
- `Ground.fpSimple_sq_integer_of_weaklyIntegral`,
  `simple_fpDimension_sq_integer_of_weaklyIntegral`, and
  `generated_simple_square_integer`: weak integrality forces integer squares
  of simple FP dimensions, including the generated-category corollary.
- `Ground.generatedCategoryAbelian`, `generatedCategoryFusion`, and
  `generatedFusionCategory`: the full tensor subcategory generated by any
  object has a genuine braided fusion-category structure;
  `generatedFusionCategory_fpDimension` proves its inclusion preserves FP dimensions.
- `Ground.balanced_flow_no_entry`, `balanced_flow_cycle`,
  `fusionFlow_balance`, `unit_retract_tensorPower`,
  `simple_generatedBy_rightDual`, and `simple_generatedCategoryRigid`:
  every simple has the unit as a retract of a positive tensor power, and its
  generated tensor subcategory is rigid; `generatedBy_rightDual` and
  `generatedCategoryRigid` extend this to every object using semisimplicity.
- `Ground.simple_functor_obj`, `simple_labels_inclusion`, and
  `globalFPDimension_le_of_full_functor`: a full faithful linear tensor
  inclusion sends simples injectively to simples and its global FP dimension
  is bounded above by that of the ambient category.
- `Ground.fpDimension_biproduct`, `fpDimension_functor_decomposition`, and
  `fpDimension_functor`: finite sums are additive, and every faithful additive
  strong monoidal functor preserves FP dimensions of all objects.
- `Ground.dual_multiplicity`, `fpDimension_leftDual`, and
  `fpDimension_rightDual`: FP dimensions of arbitrary objects are invariant
  under either dual.

The legacy `FusionData` results are separate from the bundle-free ground results.

## In progress

The round-2 induction and Maschke constructions are in progress. The centre
fusion property and global FP-square formula have been reduced to explicit
categorical identities, and proved in rank one assuming centre rigidity; see
Round 2 progress below for precise theorem statements.

## Blocked / outstanding

- Fusion-owned: prove the weighted-loop sliding identity for the constructed
  induction functor and establish the centre fusion structure. The actual
  induction functor and its right adjunction to forget are now constructed.
- Fusion-owned: prove `SimpleLoopCentrality`, the sliding equation for the
  explicit spherical weighted loop sum. The unit-labelled case and rank-one
  special case are proved; for a general simple test strand this requires the
  fusion-basis completeness and pivotal trace sliding identity. Once proved,
  the loop sum splits centre monos and epis and yields finite semisimplicity.
- Centre: construct rigidity on the actual Mathlib centre. Dimensions: produce
  a spherical structure on pseudo-unitary C; nonzero global dimension follows
  from pseudo-unitarity and FP positivity.

There is no credible completion-time estimate for the general loop-sliding proof. The existing conditional results do not
prove the frozen target. The global subcategory inequality is proved, but no
stronger divisibility theorem is claimed. Ground constructions avoid the old
hypothesis bundles; the separate compatibility bridge constructs `FusionData`.

## Latest verification

- Focused Lake builds passed for `Fusion.FunctorDimension`,
  `Fusion.SemisimpleSplit`, `Fusion.SubcategoryDimension`, `Fusion.BalancedFlow`,
  `Fusion.GeneratedRigidity`, `Fusion.GeneratedStructure`, and
  `Fusion.WeakIntegrality`, with `LEAN_NUM_THREADS=4` and cores 4–7.
- `#print axioms` for the principal new results showed only `propext`,
  `Classical.choice`, and `Quot.sound`. Integration’s strict private-body
  dependency scanner passed for `generatedFusionCategory`,
  `generated_simple_square_integer`, `unit_retract_tensorPower`, and
  `fpDimension_functor`.
- The main target is still unproved; its outstanding spherical, centre, and
  braid-rigidity obligations belong to the other workstreams.

## Round 2 progress (2026-10-27)

- `CentreInduction.crossingCandidate` is the explicit induction crossing,
  now proved natural in both arguments, normalized at the tensor unit, and
  tensor-compatible (`crossingCandidate_tensor`). The tensor proof composes
  dual mates and individual crossing blocks, refines basis contractions
  across the nested fusion decomposition, and rearranges the finite sums.
  `weak_isIso` supplies invertibility from rigidity, and
  `halfBraidingOfCrossingCandidate` constructs the actual half-braiding
  without extra assumptions. `induction` is the resulting functor from C to
  Mathlib's actual `Center C.Obj`, with underlying object the desired finite
  sum. `unitCandidate_central` proves the candidate unit is a centre map,
  and `actualAdjunction` constructs the actual right adjunction to forget.
  `globalFPDimension_square_of_actual_induction` proves the global FP-square
  identity whenever the actual centre is rigid and fusion. `center_artinian`
  and `center_noetherian` establish both chain conditions unconditionally;
  every nonzero centre object has a simple subobject, and every simple embeds
  into an induced base simple (`simple_mono_induced_simple`).
  `finite_simple_representatives` now proves finitely many actual centre
  simples up to isomorphism without sliding or sphericality, using finite
  length and the adjunction. `induction_injective` and
  `center_enough_injectives` show induced objects are injective and every
  centre object embeds in one. `center_fusion_of_nonzero_induced_trace`
  gives an alternative to loop sliding: given centre rigidity, a pivotal
  structure on the centre and nonzero trace of one induced object imply
  semisimplicity and fusion. `induced_unit_dimension` computes the underlying
  trace as FPdim(C) for a positive base pivotal structure, and
  `center_fusion_of_positive_compatible_pivotal` reduces fusion to one
  explicit trace-compatibility equality for a centre pivotal structure.
  `center_induction_retract_of_positive_compatible_pivotal` also splits the
  actual adjunction unit for every centre object under the same assumptions.
  Constructing that pivotal structure/compatibility or proving averaging-loop
  sliding remains open.
  `crossing_counit_offdiag` and `crossing_counit_diagonal` calculate its
  unit-counit column on simple test strands. `crossingUnitBlock_eval` proves
  the diagonal duality contraction, and `secondTriangle` proves the second
  triangle for the actual induction functor.
- `CentreInduction.transposeUnderlying` constructs the candidate linear Hom
  transpose and proves it injective; composing it with the unit-summand
  counit recovers the original map. Centrality and surjectivity onto centre
  morphisms remain open.
- `CentreInduction.adjunctionOfHalfBraiding` assembles the actual right
  adjunction from a half-braiding on every underlying induction sum, its
  naturality in the middle factor, centrality of `unitCandidate`, and the
  explicit second triangle. `fusion_and_globalFPDimension_of_halfBraiding`
  combines these with loop sliding and centre rigidity to construct the
  centre fusion instance and its FP-square theorem. The listed categorical
  conditions include loop sliding, which remains unproved; the half-braiding,
  unit centrality and second triangle are supplied by the actual constructions.
- `CentreInduction.unitCandidateNatural` constructs a natural map from the
  centre forgetful functor to its composite with the underlying induction
  functor, by coevaluating each simple and applying the given half-braiding.
  Its centrality and both triangle identities are now proved, giving
  `actualAdjunction`.
  `unitCandidate_counit_component` reduces the underlying first triangle to
  its unit-labelled component, and `coevaluation_iso_unit` proves the needed
  normalization of that component’s coevaluation under a unit isomorphism.
  `unitCandidate_counit` now proves the first triangle for these underlying
  natural transformations, without assuming centre induction.
- `CentreInduction.fusion_of_pseudoUnitary_and_induction` discharges
  the nonzero global-dimension premise using pseudo-unitarity and FP positivity.
  The spherical structure and sliding equation remain explicit premises;
  `actualAdjunction` supplies the induction adjunction.
- `CentreInduction.unitSummandRetract` gives an explicit retract of every
  base object from its underlying induction sum through the unit-labelled
  component. `underlyingCounit` and `underlyingUnitSummand` construct the
  projection and inclusion naturally in the object, with their composite equal
  to the identity. Their connection to the centre adjunction remains open.
- `CentreInduction.loopSum_comm_unitIndex` proves loop sliding on the unit
  test strand. `simpleLoopCentrality_of_rank_one` proves the entire sliding
  condition in fusion rank one; `centerForgetEquivalenceOfRankOne` constructs
  an actual equivalence of the centre with C in that special case.
  `rightAdjointOfRankOne` and `adjunctionOfRankOne` construct its right
  adjoint and identify its underlying object with the induction sum.
  `fusion_of_rank_one` and `globalFPDimension_square_of_rank_one` prove the
  centre fusion structure and FP-square formula for rank one, conditional
  only on centre rigidity.
- `CentreInduction.subobjectEndRangeEmbedding` embeds the subobject order
  into subspaces of a finite-dimensional Hom space when subobjects split.
  Assuming loop sliding, centre objects are Artinian and Noetherian, and
  every nonzero centre object has a simple retract.
- `CentreInduction.center_finite_simple_sum_of_loop_centrality` proves every
  centre object is a finite iterated binary sum of simple objects under the
  same explicit assumptions, by induction on endomorphism-space dimension.
  `finiteSimpleSum_biproduct` converts the binary sums into finite indexed
  biproducts.
- `CentreInduction.finite_simple_labels_of_adjunction_and_loop` proves a finite
  set of actual centre simples covers all simple objects, using the explicit
  unproved right adjoint and loop-sliding identity. The result does not
  construct either assumption. `finite_semisimple_of_adjunction_and_loop`
  deduplicates these labels and groups multiplicities into the exact ground
  fusion interface; `fusion_of_adjunction_and_loop` supplies the fusion
  instance once centre rigidity is supplied.
- `globalFPDimension_square_of_assembled_fusion` combines that instance
  with the FP-square calculation, still assuming the adjoint, the induction
  object isomorphisms, and the loop-sliding identity.
- `CentreInduction.retract_of_adjunction_and_loop` derives the required
  centre-object retract from the forgetful right adjoint and the same unproved
  loop-sliding identity, using faithfulness of forget.
- `CentreInduction.partialTraceHom`, `winding`, and `loopSum` construct the
  spherical loop average; `loopSum_center_hom` proves it acts by global
  dimension on central maps. Centrality of its action on arbitrary maps,
  needed for Maschke averaging, is not yet proved. The loop sum commutes
  with central maps on both sides; `epi_splits_of_loop_centrality` and
  `mono_splits_of_loop_centrality` prove every centre epi and mono splits
  assuming the explicitly stated finite sliding identity, spherical structure,
  and nonzero global dimension.
- `CentreInduction.comm_of_simples` proves that a candidate centre morphism
  need only satisfy the intertwining equations on base simple representatives;
  `natTrans_ext_on_simples` gives the parallel result for natural transformations
  between additive functors.
- `CentreInduction.underlyingFunctor` constructs the induction sum as a
  functor on the base category; it is additive, complex-linear, and faithful.
- `CentreInduction.homLinearEquivOfAdjunction` and
  `globalFPDimension_square_of_adjunction` derive the finrank condition from
  an actual adjunction to the forgetful functor; centre fusion/rigidity and
  the induction functor with its underlying decomposition remain premises.
- `CentreInduction.globalFPDimension_square_of_induction` derives the centre
  global FP square from centre fusion/rigidity, induced representatives with
  the stated underlying objects, and the precise adjunction Hom-dimension
  equality; these hypotheses are not yet constructed.
- `CentreInduction.underlying` constructs the underlying finite biproduct;
  `CentreInduction.fpDimension_underlying` proves its FP dimension equals
  `globalFPDimension C * fpDimension C X`. Focused build passes.

## Round 2 plan (2026-10-27)

Use the actual Mathlib centre and its forgetful functor, with the existing
`Integrate.bundledCenter` once centre rigidity and the fusion instance are supplied.
Construct the underlying induction object as the finite biproduct of
`Sᵢ ⊗ X ⊗ Sᵢ*` and prove its FP dimension directly by additivity,
multiplicativity and dual invariance. Construct its canonical half-braiding
using simple-decomposition matrix units, prove the adjunction with forget,
and split its unit/counit by the nonzero global dimension. The splitting should
give semisimplicity and a finite set of simple summands of induced simples.
Finally use adjunction and the FP dimension of induced objects to compare the
regular FP vectors and obtain the global square formula. Centre already
provides finite-dimensional Hom spaces and the unit-endomorphism comparison.
The induction half-braiding and adjunction are constructed; the loop-sliding
identity remains substantial work. The averaging splitting and centre fusion assembly are
proved conditionally on those inputs and the stated spherical assumptions.

## Round 2 verification

Focused builds passed for `CentreInduction.Fusion`, `RankOne`, `UnitSummand`,
and `PseudoUnitary`, including their dependency modules. `#print axioms` on
the finite-semisimplicity assembly, conditional centre fusion and FP-square
theorems, rank-one sliding and FP-square theorems, and pseudo-unitary assembly
showed only `propext`, `Classical.choice`, and `Quot.sound`. The explicit
mathematical premises described above are still unproved.

- The root module `PropertyF.lean` was checked with `lake env lean` after
  building missing dependencies one at a time; it passed. The integrated
  `ProjectAudit` build audited 3,250 imported declarations and passed.
  `#print axioms` for the crossing naturality and completeness, first triangle,
  conditional adjunction/fusion/FP-square, and rank-one FP-square results
  returned only `propext`, `Classical.choice`, and `Quot.sound`. These checks
  do not discharge the explicit general induction and sliding premises.

## Round 2 latest verification

Focused builds passed for `InducedTrace` and its dependencies; the root
`PropertyF.lean` checked successfully using the assigned cores. `#print axioms`
for `induction`, `actualAdjunction`, `finite_simple_representatives`,
`center_enough_injectives`, `globalFPDimension_square_of_actual_induction`,
and `center_fusion_of_positive_compatible_pivotal` reported only
`propext`, `Classical.choice`, and `Quot.sound`. The latter fusion result
still assumes the explicit centre pivotal trace compatibility, and the FP
square assumes centre rigidity and fusion.
