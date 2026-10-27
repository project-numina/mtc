# Centre workstream status

## Round 2 route

For an arbitrary centre object, take its underlying right dual and obtain the
crossing by taking the rigid mate of the given half-braiding, normalized at the
unit. Its tensor law and the evaluation/coevaluation intertwining equations
must be proved from the half-braiding law and the zig-zag identities; the
normalization alone proves neither. The centre is braided, so one right dual
per object also supplies a left dual. For the bundle use the existing exact
abelian and linear centre instances, inject centre Hom spaces into finite base
Hom spaces, and use the established simple unit. Fusion owns the genuinely
remaining finite semisimple decomposition of the actual centre, via induction
and separability; bundle it against these same canonical instances. No product
image dominance is assumed.

## Route

Mathlib constructs the braided monoidal Drinfeld centre and the positive monoidal embedding. For the fusion and dimension theorem the candidate elementary route is the induction functor, built using a finite semisimple decomposition as a coend, followed by its adjunction to the forgetful functor and the dimension computation. The coend construction, semisimplicity of the centre, pivotal traces, and nondegeneracy are substantial missing proofs; induction is a proposed route, not a result. The Deligne tensor product and its universal property are also absent. Unconditional dominance of C ⊠ C^rev → Z(C), requested in the workstream brief, is false: for C = Rep_C(Z/2) the positive and negative embeddings agree and the product image has only two simple objects, whereas the centre has four. Dominance requires an additional nondegeneracy assumption. This does not change the frozen target.

## Done

`PropertyF.Ground.Centre.negative` is the reverse-braiding monoidal embedding; `positiveFaithful`, `positiveFull`, `negativeFaithful`, `negativeFull` prove the two embeddings fully faithful; `positive_negative_centralize` proves their images centralize in the actual Drinfeld centre. `positiveBraided` and `negativeBraided` establish compatibility with the source braidings, including the reversed braiding. `centralizes_positive_image_iff`, `centralizes_negative_image_iff`, `negativeIsoOfCentralizesPositive`, and `positiveIsoOfCentralizesNegative` give the mutual-centralizer calculation using actual centre morphisms and explicit isomorphisms. `centralizes_positive_iff_negative_essential_image` and `centralizes_negative_iff_positive_essential_image` identify both categorical centralizers up to isomorphism; `transparent_iff_positive_in_negative_image` identifies their intersection with transparent objects. Mathlib already provides `Center`, its braided monoidal structure, `Center.forget`, and `Center.ofBraided`; the baseline proves the objectwise equivalences in `PropertyF.CenterBasics`.

The centre has a constructed preadditive structure, linear structure over any ring, monoidal preadditive/linear structures, and faithful additive/linear forgetful functor in `PropertyF.Ground.Centre.Linear`; `finiteDimensional_hom` proves finite-dimensionality of centre Hom spaces from that of the underlying Hom spaces. `centerZero` equips the zero object of C with its unique half-braiding, and `centerHasZeroObject` supplies a zero object of the centre; `isZero_of_forget` shows the forgetful functor detects zero objects. `centerBiprod` constructs the sum half-braiding and lifts its biproduct bicone, yielding `centerHasBinaryBiproducts` and `centerHasFiniteBiproducts`. Both canonical embeddings are linear; `unitHomLinearEquiv` identifies the unit endomorphism spaces through the forgetful functor.

`reverse_braidGenerator`, `reverse_braidImage`, and `reverse_objectPropertyF_iff` prove that the actual adjacent generators invert under reverse braiding, the generated image subgroup is unchanged, and objectwise property F is invariant.

`mixedBraiding` constructs the componentwise braiding with the second component reversed on the ordinary product category. `productFunctor` constructs the monoidal functor from this ordinary product category to the centre and `positiveProductIso` / `negativeProductIso` identify its restrictions to the two factors. `productBraided` proves this functor is braided for `mixedBraiding`. `productFunctor_image_quotient` and `productFunctor_retract_image_quotient` construct the subgroup-to-image surjection for any image and any retract, and `productFunctor_retract_objectPropertyF` transfers property F. `ProductRetract` is proved closed under retracts, binary sums, and tensor products; it contains the unit and both canonical images, and has property F when C does. This is not yet the Deligne product; `ProductTensorClosure` explicitly generates the unit and canonical images under tensor, binary sums and retracts; `productTensorClosure_image_quotient` and `productTensorClosure_propertyF` discharge the product-image and property-F conclusions for every object in that closure. Dual closure and identification with the generated fusion subcategory remain open.

`productFunctor_finiteSumRetract` constructs a single product image containing any finite sum of product images as a retract. `productRetract_finiteBiproduct` and `productRetract_tensorPower` give the corresponding finite-sum and power closure, and `productRetract_generatedBy` proves closure under all objects generated by any product retract in the actual centre of a rigid abelian base. Fusion's dual-generation theorem can yield dual closure once a genuine fusion-category structure on the centre is constructed and its categorical instances are aligned.

`positiveExactPairing`, `negativeExactPairing`, and `productImageExactPairing` construct dual pairs in the centre for both canonical images and their product images. These use actual evaluation and coevaluation maps and do not assume that arbitrary centre objects have duals. Extending duality to retracts remains open; arbitrary centre objects are not in general retracts of product images, as the symmetric example above shows.

`fstBraidMap`, `sndBraidMap`, `productBraidMap`, `productBraidMap_injective`, and `product_braidImage_finite` prove that actual braid images of objects in the mixed product category embed in the product of the factor images, so finite images of both factors imply a finite product image. The proof uses the merged modular workstream’s braided-functor coherence. `positive_objectPropertyF_iff` and `negative_objectPropertyF_iff` establish property F preservation and reflection by both canonical embeddings.

`centerKernel` and `centerKernelIsLimit` construct kernels in the centre of a rigid abelian monoidal category. `centerForgetPreservesMonomorphisms` follows from this construction, and `centerSimple_of_underlying` proves that a centre object is simple whenever its underlying object is simple. In particular `centerUnitSimple`, `positive_preserves_simple` and `negative_preserves_simple` establish simplicity of the unit and the canonical images of simple objects.

`centerCokernel` and `centerCokernelIsColimit` construct cokernels in the centre; `centerForgetPreservesEpimorphisms` proves the forgetful functor preserves epimorphisms. `centerNormalMono`, `centerNormalEpi`, and `centerAbelian` prove that the centre of a rigid abelian monoidal category is abelian.

`centerForgetPreservesKernel` and `centerForgetPreservesCokernel` show that the constructed centre kernels and cokernels are sent to the underlying ones. Consequently `centerForgetPreservesFiniteLimits` and `centerForgetPreservesFiniteColimits` give exactness of the forgetful functor.

`integral_of_nonnegative_falling_factorials` proves the arithmetic step for an elementary exterior-power proof of symmetric-core integrality: a nonnegative real whose falling factorials are all nonnegative is a natural number. Proving that these falling factorials are factorial multiples of actual exterior-power dimensions in the pseudo-unitary symmetric core remains open.

`groupAverage_idempotent` and `algebraAverage_idempotent` establish finite-group averaging as an idempotent in any algebra over a commutative ring with invertible group order. `alternatingProjector`, `alternatingProjector_eq_sum`, and `alternatingProjector_idempotent` specialize this to the sign character of a symmetric group. `alternatingProjector_splits` constructs the split image in an idempotent-complete linear category, and `alternatingProjector_dimension_formula` identifies its pivotal dimension with the normalized signed sum of traces of the action operators. This does not yet construct the symmetric-group action on tensor powers or evaluate those operator traces.

`objectPropertyF_of_symmetricGroup_actions` proves the property-F consequence of an explicit symmetric-group action whose adjacent transpositions act by the actual braid generators. The action itself is a premise, and is not yet constructed even for the vector-space test category.

`CentreBundle.fusionOfFiniteSemisimple` assembles the actual centre fusion
interface from centre rigidity and the explicit finite semisimple decomposition;
finite Hom spaces and simple unit are proved from C. This is conditional on
the stated decomposition, which fusion owns, and on centre rigidity.

`CentreRigid.dualObject`, `liftedPairing`, and `rigidOfMateCoherence`
construct the actual centre duals and rigidity conditional on the explicit
three mate-coherence equations. Triangle identities are proved by forgetting,
and the chosen right evaluation and coevaluation forget to the original maps
by definition. `dualCrossing_tensor_unit_left` and
`dualCrossing_tensor_unit_right` prove both unit cases of the crossing tensor
law from naturality and unit normalization. `halfBraiding_unit` and
`centrality_at_unit` prove the evaluation and coevaluation intertwining
equations at the tensor unit, for any underlying morphism. The general tensor law and both
centrality equations remain unproved. `dualMate_counit` and `dualMate_unit`
expose the mate identities for use in those coherence proofs.

## In progress

Prove `ProductRetract` is closed under duals and agrees with the generated fusion subcategory; investigate centre rigidity and semisimplicity. For the exterior-power route construct the symmetric-group action and compute the trace of the alternating projector; Mathlib does not appear to provide the needed action or symmetric-group presentation directly.

## Blocked / dependencies

Integrate's genuine category interface and fusion's finite-semisimplicity and dual-generation theorems are available. The centre is not yet bundled into that interface: the half-braiding on the dual of an arbitrary centre object, the finite semisimple centre decomposition and the induction/coend construction remain centre-owned work. Dimensions has pivotal traces but the canonical positive spherical structure remains unconstructed; modular supplies the categorical S-matrix results assuming an actual centre fusion category and invertibility; calculus owns the braid-algebra realization and its trace recurrence. These dependencies are not discharged merely by importing the respective branches.

## Remaining fields

The rest of centre fusion/spherical structure (in particular rigidity, semisimplicity, and finite simple objects) and categorical/FP dimension formulas; modularity; symmetric integrality; double centralizer; `global_square`, `symmetric_integrality`, `double_centralizer`, `product_witness`, and centre instances/data/dimensions in `CenterInputs`. `realize` additionally depends on calculus. No individual field has been discharged yet.

## Estimate

The foundational fusion, pivotal, semisimplicity, induction and nondegeneracy developments are extensive research-scale formalization work; completion cannot responsibly be estimated in hours. Begin with independently provable categorical structure while interfaces mature.

## Round 2 verification

Focused Lake builds passed for `CentreBundle.Fusion`, `CentreRigid.Lift`,
`CentreRigid.Unit` and `CentreRigid.MateEquations` on cores 16–19. Lean
`#print axioms` reports only propext, Classical.choice and Quot.sound for
the fusion assembly, conditional rigidity, both unit tensor laws, unit
centrality, and both mate equations. The general mate coherence remains
centre-owned work, not an external dependency.

## Round 3 continuation

Merged the integration snapshot including induction, rank-one results and current
centralizer reductions. General rigidity remains the priority. In
`CentreRigid.SimpleCentrality`, `coevaluation_central_of_simples` and
`evaluation_central_of_simples` reduce the two duality-map centrality equations
to tests on base simple representatives, once the crossing tensor law is given.
This is a reduction, not a proof of those tests or of rigidity. The immediate route
is to use naturality and semisimple decompositions similarly for the tensor law,
then prove the resulting mate equations diagrammatically.
`dualCrossing_tensor_of_simples` also proves the general tensor law follows
from its cases on pairs of base simple representatives, by naturality in each
argument and semisimple decomposition. The simple-pair cases are not proved.
`tensor_of_rank_one` and `rigidOfRankOne` prove the normalized mate tensor law
and centrality in rank one, constructing rigidity with base right duals and
base evaluation/coevaluation definitionally. This strengthens the rank-one
comparison with the previously constructed equivalence-based instance; it
has no implication for general rank. The focused build passes and the main
instance has only the three standard Lean axioms.
`dualMate_counit_explicit` and `dualMate_unit_explicit` express the abstract
mate equations through the actual cups and caps. Moreover,
`dualMateUnit_crossed_coevaluation` identifies the unit normalization with the
crossed coevaluation: the base right-dual cup followed by the half-braiding
is the base left-dual cup followed by the normalization map. This is a concrete
step toward the general centrality and tensor diagrams, not their proof.
`coevaluation_sliding` proves the normalized dual crossing intertwines the base
coevaluation in every rigid monoidal category, without any tensor-law premise;
`coevaluation_central` lifts this to the actual centre once the crossing tensor
law is supplied. The proof uses the mate unit, half-braiding naturality and
tensor law, and the crossed-cup normalization. Evaluation and the dual-crossing
tensor law remain open. Focused Lake build passes on cores 16–19.
`dualCrossing_tensor` proves the general normalized dual crossing tensor law
in every rigid monoidal category. The proof composes two coevaluation slides,
uses interchange and the original half-braiding law, then invokes injectivity
of the rigid Hom equivalence. Together with `coevaluation_central`, only
centrality of evaluation remains before general centre rigidity. Focused build
passes; the proof has no additional hypotheses.
`evaluation_sliding` and `evaluation_central` prove the remaining cap diagram,
and `rigidCenter` constructs `RigidCategory (Center C)` for every rigid
monoidal category, without further premises. `rigidCenter_forget_dual`,
`rigidCenter_forget_evaluation`, and `rigidCenter_forget_coevaluation` record
that its chosen dual and pairing forget definitionally to those of the base.
Focused Lake build passes. General centre finite semisimplicity and fusion
assembly remain to be completed; rigidity is no longer a dependency.
For `rigidCenter`, `forgetDualIso_eq_refl` and `forgetDoubleDualIso_eq_refl`
identify fusion's canonical centre/base dual comparison isomorphisms with the
identity, simplifying the induced pivotal-centrality calculation. Focused
build passes; the needed pivotal centrality and base positive sphere are open.
`canonicalFusionOfFiniteSemisimple` and `bundledOfFiniteSemisimple` now use
`rigidCenter` directly; `globalFPDimension_bundledOfFiniteSemisimple` proves
the FP square using the actual induction adjunction. Their sole remaining
premise is the explicit finite-semiplicity decomposition. Focused build passes.
For the separate Kirby-loop route, `partialTraceHom_dinatural` proves a
morphism can be moved around the closed strand of a pivotal partial trace,
and `partialTraceHom_conjugate` proves invariance under changing the closed
object by an isomorphism. These hold for arbitrary pivotal categories and
are tools toward, not proofs of, general loop sliding. Focused build passes.
`partialTraceHom_biproduct` decomposes a partial trace over a finite biproduct
into its diagonal partial traces. `winding_natural`, `trace_winding_biproduct`
and `trace_winding_simple_decomposition` show the actual centre winding
trace is additive in the test strand and give its simple fusion-multiplicity
expansion. These are ingredients for Kirby-loop sliding, which remains open.
`fp_loop_absorption` proves that the FP-weighted sum of closed windings over
`S_k ⊗ S_i` equals `FPdim(S_k)` times the original sum. With FP-valued
pivotal dimensions, `loop_absorption` identifies the sum as the actual
Kirby loop. The geometric sliding identity is still missing.
`winding_tensor` factors winding around a tensor product into successive
windings; `trace_inner_winding_tensor` closes the inner factor and produces
the outer winding of that partial trace. To combine this with FP absorption,
one still needs the general nested partial-trace identity (existing
`rightPartialTrace_nested_simple` only handles simple equal survivors) and
the open-strand geometric sliding identity.
`partialTraceHom_nested` proves the general iterated partial-trace identity
for arbitrary surviving objects and maps, using `cap_tensor` and the canonical
tensor dual pairing. This removes the nested-trace gap in combining the
winding tensor factorization with FP loop absorption. The geometric step from
closed-loop absorption to open-strand centrality remains unproved. Focused
build passes.
`closedWinding_tensor` proves closed windings compose under tensor product;
`loop_eigen` proves the Kirby loop is a common FP eigenvector for all simple
closed winding maps; `loop_square` and `normalized_loop_idempotent` prove its
normalization is idempotent on underlying Hom spaces. No loop centrality or
centre semisimplicity is claimed: identifying its image with centre Hom maps
remains the missing geometric step. Focused build passes.
`negative_and_induced_detect_unit` proves a simple object of the actual centre
centralizing all negative images and the actual induced tensor unit is
isomorphic to the centre unit. Consequently `transparent_simple_is_unit`
proves categorical nondegeneracy of the actual centre, without centre fusion,
pivotal or spherical assumptions. The proof uses the nonzero diagonal matrix
block of the actual induction crossing and the counit unit-summand projection.
Numerical S-centrality has not yet been shown to imply categorical centrality;
therefore S-matrix invertibility is not claimed. Focused build passes.
`center_s_invertible_of_test_monodromy` proves categorical S invertibility for
an FP-valued pivotal centre assuming finite-order mixed monodromies only for
test simples that are retracts of negative images or of the induced unit, and
only against numerical S-central labels. The proof combines categorical centre
nondegeneracy with positive trace saturation and the existing S criterion.
Those finite-order hypotheses remain unproved; this is not unconditional S
invertibility. Focused build passes.
