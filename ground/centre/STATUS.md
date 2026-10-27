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
