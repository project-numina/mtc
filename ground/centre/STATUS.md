# Centre workstream status

## Route

Mathlib constructs the braided monoidal Drinfeld centre and the positive monoidal embedding. First construct the reverse-braiding embedding and prove the mutual-centralizer calculation at the actual functor level. For the fusion and dimension theorem the candidate elementary route is the induction functor, built using a finite semisimple decomposition as a coend, followed by its adjunction to the forgetful functor and the dimension computation. The coend construction, semisimplicity of the centre, pivotal traces, and nondegeneracy are substantial missing proofs; induction is a proposed route, not a result. The Deligne tensor product and its universal property are also absent and must be built before the full product functor can be stated. No assumption that these constructions exist should be mistaken for a proof.

## Done

`PropertyF.Ground.Centre.negative` is the reverse-braiding monoidal embedding; `positiveFaithful`, `positiveFull`, `negativeFaithful`, `negativeFull` prove the two embeddings fully faithful; `positive_negative_centralize` proves their images centralize in the actual Drinfeld centre. `positiveBraided` and `negativeBraided` establish compatibility with the source braidings, including the reversed braiding. `centralizes_positive_image_iff`, `centralizes_negative_image_iff`, `negativeIsoOfCentralizesPositive`, and `positiveIsoOfCentralizesNegative` give the mutual-centralizer calculation using actual centre morphisms and explicit isomorphisms. `centralizes_positive_iff_negative_essential_image` and `centralizes_negative_iff_positive_essential_image` identify both categorical centralizers up to isomorphism; `transparent_iff_positive_in_negative_image` identifies their intersection with transparent objects. Mathlib already provides `Center`, its braided monoidal structure, `Center.forget`, and `Center.ofBraided`; the baseline proves the objectwise equivalences in `PropertyF.CenterBasics`.

The centre has a constructed preadditive structure, linear structure over any ring, monoidal preadditive/linear structures, and faithful additive/linear forgetful functor in `PropertyF.Ground.Centre.Linear`; `finiteDimensional_hom` proves finite-dimensionality of centre Hom spaces from that of the underlying Hom spaces. `centerZero` equips the zero object of C with its unique half-braiding, and `centerHasZeroObject` supplies a zero object of the centre; `isZero_of_forget` shows the forgetful functor detects zero objects. `centerBiprod` constructs the sum half-braiding and lifts its biproduct bicone, yielding `centerHasBinaryBiproducts` and `centerHasFiniteBiproducts`. Both canonical embeddings are linear; `unitHomLinearEquiv` identifies the unit endomorphism spaces through the forgetful functor.

`reverse_braidGenerator`, `reverse_braidImage`, and `reverse_objectPropertyF_iff` prove that the actual adjacent generators invert under reverse braiding, the generated image subgroup is unchanged, and objectwise property F is invariant.

`mixedBraiding` constructs the componentwise braiding with the second component reversed on the ordinary product category. `productFunctor` constructs the monoidal functor from this ordinary product category to the centre and `positiveProductIso` / `negativeProductIso` identify its restrictions to the two factors. `productBraided` proves this functor is braided for `mixedBraiding`. This is not yet the Deligne product; extension and dominance remain open.

`fstBraidMap`, `sndBraidMap`, `productBraidMap`, `productBraidMap_injective`, and `product_braidImage_finite` prove that actual braid images of objects in the mixed product category embed in the product of the factor images, so finite images of both factors imply a finite product image. The proof uses the merged modular workstream’s braided-functor coherence. `positive_objectPropertyF_iff` and `negative_objectPropertyF_iff` establish property F preservation and reflection by both canonical embeddings.

## In progress

Extend the braided product functor to the Deligne product; transport braid images through the embeddings; investigate centre rigidity and semisimplicity.

## Blocked / dependencies

The frozen genuine fusion-category interface is being developed by integrate; finite semisimple machinery by fusion; pivotal/spherical traces and canonical pseudo-unitary structure by dimensions; modular-data constructions by modular; simultaneous braid-algebra realization by calculus. Need their precise interfaces before constructing the centre-specific portions of `CenterInputs`.

## Remaining fields

The rest of centre fusion/spherical structure (in particular rigidity, semisimplicity, finite simple objects, and simple unit) and categorical/FP dimension formulas; modularity; symmetric integrality; double centralizer; `global_square`, `symmetric_integrality`, `double_centralizer`, `product_witness`, and centre instances/data/dimensions in `CenterInputs`. `realize` additionally depends on calculus. No individual field has been discharged yet.

## Estimate

The foundational fusion, pivotal, semisimplicity, induction and nondegeneracy developments are extensive research-scale formalization work; completion cannot responsibly be estimated in hours. Begin with independently provable categorical structure while interfaces mature.
