# Modular workstream status

## Done

- `PropertyF.Ground.Modular.Character.map`, `galoisPerm`, `galoisLabel`, and `galoisLabel_character`: construct the genuine action of every automorphism of ℂ on characters of integral fusion rules, then transport it to labels via a classification of those characters.
- `PropertyF.Ground.Modular.characters_exhausted`, `characters_bijective`, `dual_involutive`, and `normalized_columns_linearIndependent`: normalized columns classify all characters from S symmetry, S-square, nonzero dimensions and the Verlinde character equations.
- `PropertyF.Ground.Modular.modularDataOfVerlinde` constructs `ModularData` from the S identities and Verlinde character equations, deriving both classification and Galois fields.
- `PropertyF.Ground.Modular.modularDataOfCharacters`: constructs the existing `ModularData` package from its numerical identities plus a bijective classification of normalized S-columns as fusion characters. The Galois permutation and its character equation are constructed, not supplied.
- `PropertyF.Ground.Modular.braidGenerator_natural`, `conjugate_braidGenerator`, and `braidImageIso`: isomorphic objects have isomorphic braid-image groups via the actual tensor-power isomorphisms; this requires only a braided monoidal category.
- `PropertyF.Ground.Modular.braidGenerator_functor`, `braidImageFunctorIso`, `braidImages_of_essentiallySurjective`, and `conjugate_images`: the old `StandardInputs.conjugate_images` field is proved from the braided equivalence; the general result works for any faithful, essentially surjective braided monoidal functor without old hypothesis structures.
- `PropertyF.Ground.Modular.simpleLabels_equiv` constructs the bijection of simple representatives under any category equivalence for the frozen ground category, together with the actual object isomorphisms.
- `PropertyF.Ground.Modular.conjugate_hom_finrank`, `conjugate_fusionCoeff`, `conjugate_fusionMatrix`, `conjugate_fpSimple`, `conjugate_labels`, and `conjugate_globalFPDimension`: Galois conjugacy preserves Hom dimensions, fusion rules, target spectral-radius FP dimensions, and global FP dimension. These statements use the frozen ground category and no old hypothesis bundles.
- `PropertyF.Ground.Modular.ground_conjugate_images` and `conjugate_propertyF`: braid images and property F transport to the conjugate in the frozen ground interface.
- `PropertyF.Ground.Modular.categoricalS`, `categoricalS_symmetric`, `categoricalS_unit`, and `categorical_global_eq_sum_squares`: the actual double-braiding trace defines S for a ground braided fusion category with a pivotal structure; symmetry and unit column follow without nondegeneracy, and global sum-of-squares follows from sphericality.
- `PropertyF.Ground.Modular.categoricalS_galois_action` constructs the Galois action on the actual S columns from explicitly stated S-square, global-dimension nonvanishing, and Verlinde equations, with no old modular-data bundle; `galois_unit_properties` proves the paper's Proposition 2.1 from the exact numerical identities.
- `PropertyF.Ground.Modular.Audit` privately imports project modules and passes the integrator's hardened fail-closed dependency scanner and foundational-axiom check for ground Galois reduction, braid-functor surjectivity, S symmetry/unit, simple-dimension nonvanishing, and the Galois action and proposition. This audit checks the declarations, not the missing final theorem.
- `PropertyF.Ground.Modular.braidImageFunctorMap`, `braidImageFunctorMap_surjective`, and `objectPropertyF_functor`: arbitrary braided functors, including nonfaithful ones, induce surjections on braid images and preserve objectwise property F.
- `PropertyF.Ground.Modular.pivotalTrace_simple_ne_zero` and `simpleDimension_ne_zero`: every simple in a genuine pivotal braided fusion category has nonzero categorical dimension, from semisimple splitting and rigidity plus Schur; no spherical or pseudo-unitary hypothesis is required. `categoricalS_galois_action` now derives simple-dimension nonvanishing.
- `globalDimension_ne_zero_of_pseudoUnitary` and `categoricalS_galois_action_pseudoUnitary`: in the paper's pseudo-unitary setting, both simple and global dimension nonvanishing are derived; the remaining action hypotheses are S² and Verlinde with the actual dual-label map. `categoricalS_galois_unit_properties` specializes Proposition 2.1 and derives unit normalization.
- `trace_unit` and `simpleDimension_unit`: a pivotal structure gives unit dimension one, derived from the canonical dual-comparison coherence. `categoricalS_galois_unit_properties` no longer assumes unit normalization.
- `legacy_conjugate_labels`: constructs the exact legacy `StandardInputs.conjugate_labels` field, comparing the legacy positive character to the ground spectral-radius character via positive-character uniqueness. `conjugate_images` is also proved. The compatibility proof explicitly mentions legacy structures and is not used in the strict target cone.
- `SEntry_biproduct_left` and `SEntry_tensor_decomposition`: double-braiding traces are additive on finite biproducts and expand on tensor products with the actual Hom-space fusion coefficients. `categoricalS_verlinde_of_hopf_product` reduces the normalized Verlinde equations to the Hopf-link product identity, subsequently proved in `Verlinde.lean`.
- `partialTrace_doubleBraiding_simple` identifies the partial trace of a double braiding on a simple surviving object with its normalized S scalar, using the proved iterated-trace law. `hopf_product_of_partialTrace_composition` reduces the Hopf product to a concrete equation between partial traces of the three actual double braidings.
- `doubleBraiding_tensor_factorization`, `rightPartialTrace_natural`, `rightPartialTrace_whiskerLeft`, `rightPartialTrace_nested_simple`, `partialTrace_doubleBraiding_tensor`, and `categoricalS_verlinde`: the Hopf-link product identity and all normalized Verlinde character equations are proved from genuine braided pivotal fusion categories. `categoricalS_galois_action_of_S_square` needs only pseudo-unitarity, a pivotal structure and the S² identity.
- `character_dual_conj` proves that every normalized character respects duality and complex conjugation from fusion-coefficient reciprocity. Consequently `categoricalS_dual_conj`, `categoricalS_dual_symmetric`, and `simpleDimension_dual` hold whenever all simple pivotal dimensions are real. This is a conditional result and does not itself prove reality.
- `character_orthogonal`, `categoricalS_square`, and `categoricalS_galois_action_of_invertibleS`: from an actual spherical pivotal structure, real simple dimensions, and invertibility of the categorical S matrix, the full S² identity and Galois action are proved. `categoricalModularData` constructs every field of the legacy `ModularData` compatibility bundle from the same explicit categorical assumptions. The centre has not yet supplied those assumptions.
- `categoricalS_galois_symmetry` combines the full action with the paper's unit-column, self-duality and global-dimension Galois identities directly for the actual S matrix, under sphericality, real simple dimensions and invertible S.
- Verified: `LEAN_NUM_THREADS=4 taskset -c 20-23 lake build PropertyF` and `lake build PropertyF.Ground.Modular.Audit` under the same core/thread limits; the hardened modular proof-body and foundational-axiom audit passes.

## In progress

- Work with centre and dimensions to connect the actual centre to the proved modular-data theorems; the centre fusion/spherical structure, reality and S invertibility are not yet available.

## Blocked / dependencies

- Construction of the actual Drinfeld centre as a ground braided fusion category, its spherical structure, real simple dimensions, and invertibility of its categorical S matrix are owned by centre/dimensions and are not yet available. The S-matrix identities and Galois action are constructed once those precise inputs are supplied.
- Integrate froze the genuine-category target from `ground/integrate` commit 45da64d. Its strict audit prohibits old hypothesis structures in the final dependency cone; the category-free character and classification theorems are independent of those structures, while the two old-`ModularData` constructors are compatibility bridges only.

## Remaining

- Categorical S, symmetry, unit column, Verlinde, normalized-column classification, S-square, and the full Galois action are proved for a spherical category with real simple dimensions and invertible categorical S. Construct/obtain those properties for the actual centre.
- Ground conjugate label, spectral FP invariance, and the legacy `StandardInputs.conjugate_labels` field are complete.
- `conjugate_images` is complete; integrate its general braided-functor version into the ground proof without old hypothesis structures.

The category-level modular identities and Galois action are constructed under the stated spherical, reality and invertibility conditions. Instantiating them for the actual centre and completing the final target remain open. There is no reliable completion-time estimate until the centre fusion structure, canonical spherical dimensions and S-invertibility are constructed; these are substantial foundational dependencies, not routine wiring.

## Round 2: centre modularity and dimension

The intended elementary dimension route uses the right adjoint I of the actual centre forgetful functor: adjunction gives `[I(X_i):Z_j] = [U(Z_j):X_i]`, and the standard underlying decomposition `U I(X) = ⊕_k X_k ⊗ X ⊗ X_k*` gives `FPdim(I(X_i)) = FPdim(C) FPdim(X_i)`. Summing those equalities with FP weights and using preservation of FP dimension by U proves `FPdim(Z(C)) = FPdim(C)^2`. A positive spherical structure then identifies the categorical global dimension with the former. `CentreModular.center_globalFPDimension_of_induction` and `center_globalDimension_of_induction` prove exactly this calculation, with the adjunction multiplicities and induction sizes explicit and still unproved; no induced object is asserted to exist. Focused build passed.

For nondegeneracy, first reduce invertibility of the actual S matrix to pairwise distinct normalized S columns using their existing fusion-character orthogonality. The missing categorical step is then to show those columns separate centre simples, using the induction/coend and its Hopf-link calculation. This separation is not known from the current interfaces. Rigidity/fusion of the actual centre, the induction construction and positive spherical structure remain substantial dependencies; no reliable completion estimate is available.

`CentreModular.character_matrix_det_ne_zero` proves distinct fusion characters give an invertible evaluation matrix using Hermitian orthogonality. `categoricalS_det_ne_zero_iff_columns_injective` proves invertibility iff normalized categorical S columns separate labels, for every pivotal braided fusion category. `categoricalS_square_of_kirby` proves the full S-square identity from the explicit vacuum Kirby-loop sum `∑ z, dim(z) S(k,z) = if k = unit then D else 0`; `categoricalS_det_ne_zero_of_kirby` proves S invertible when D is nonzero. Both results avoid sphericality and positivity. The centre-specific Kirby identity is not proved; constructing it requires the half-braiding/adjunction and categorical loop calculation. `center_globalDimension_of_underlying_induction` uses fusion's actual underlying induction sum and the same positive-FP spherical dimensions required by the integration interface, alongside the explicit induction isomorphism and adjunction. Focused builds pass.

The FP-square equation alone does not prove the centre pseudo-unitary: that additionally requires the intrinsic categorical global-dimension square or an independent positive spherical construction. The existing positive spherical construction currently assumes centre pseudo-unitarity, so using it here would be circular without a separate proof.

`CentreModular.categoricalS_det_ne_zero_of_trivial_S_centralizer` sharpens the modularity route: assuming simple pivotal dimensions equal FP dimensions, it proves S invertible if the only simple satisfying `S(i,k) = dim(i) dim(k)` for every i is the unit. The proof constructs the missing Kirby-loop vanishing from orthogonality against the unit character. The actual centre's trivial S-centralizer, and the comparison between this numerical condition and actual double-braiding transparency, remain unproved. Focused build passed.

`CentreModular.regular_coeff_eigenvector`, `regular_character_sum_vanishes`, and `regular_S_transform_vanishes` prove that the FP-weighted regular element of any dual- and fusion-closed finite label set has S transform supported on its numerical S-centralizer. The S version assumes only actual pivotal dimensions equal FP dimensions, not S invertibility. This supplies cabling's requested regular-element support lemma; applying it to product-retract labels still requires their explicit finite fusion/dual closure proof. Focused build passed.

Merged fusion's actual-adjunction bridge. `CentreModular.center_globalDimension_of_adjunction` now takes the right adjoint to the actual centre forgetful functor, the underlying induction-object isomorphisms, and spherical FP-valued dimensions, and proves the categorical dimension-square formula. These premises remain open. After moving fusion's imports before the root module documentation, `LEAN_NUM_THREADS=4 taskset -c 20-23 lake build PropertyF` passes, including the integrated 3,242-declaration foundational-axiom audit. Direct `#print axioms` checks of the new dimension, S-centralizer, Kirby, and regular-support theorems show only `propext`, `Classical.choice`, and `Quot.sound`.

Merged integration d6173aa in merge 4292aac. The full `PropertyF` build now passes with the expanded 3,577-declaration integrated audit; the adjunction-based categorical dimension theorem also passes `#print axioms` with exactly the three permitted axioms. Remaining modularity obstruction: the existing trace equality `S(i,k)=dim(i)dim(k)` is a scalar equality, while actual transparency is an equality of endomorphisms. Positivity of categorical dimensions alone has not supplied an argument that upgrades this scalar equality to equality of monodromy; such an argument may need finite-order/twist information or a direct induction-loop calculation. The actual induction lift/adjunction, centre rigidity/fusion and independent positive spherical or intrinsic-dimension square are still being constructed by their respective owners. Their present absence prevents instantiating these centre-specific results and leaves no reliable completion-time estimate.

## Round 3 continuation

Merged integration snapshot 8c9e461. Fusion's actual centre induction and
forgetful adjunction are now constructed, so
`CentreInduction.globalFPDimension_square_of_actual_induction` proves the
FP square assuming only the actual centre rigidity and fusion instances.
`CentreModular.center_forget_unitScalar`, `center_pivotalDimension_eq_forget`,
`center_pivotalDimension_eq_fp_of_compatible`, `center_spherical_of_compatible`,
and `center_globalDimension_square_of_compatible` show that a pivotal centre
lift compatible with an FP-valued base pivotal structure automatically has
FP-valued dimensions, is spherical, and gives the categorical dimension square.
This does not assume centre pseudo-unitarity and uses the actual induction
adjunction; however, construction of the compatible centre pivotal lift and
centre rigidity/fusion remain open. The general Kirby-loop identity and S
invertibility remain open. Focused build passed; `#print axioms` for the scalar,
FP-value, sphericality and dimension-square results returned only propext,
Classical.choice and Quot.sound.
