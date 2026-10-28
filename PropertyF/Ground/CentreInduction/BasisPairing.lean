module
public import PropertyF.Ground.CentreInduction.CrossingBlocks
public import Mathlib.LinearAlgebra.Dual.Basis
public import PropertyF.Ground.Dimensions.DualTensorNaturality

open PropertyF.Ground.Dimensions

/-! Dual bases for the actual fusion summand inclusions and projections. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
-- Chosen simple representatives of the base category.
local notation "Sᶜ" => simples C
variable {V W : C.Obj} {E : Type*} [AddCommGroup E] [Module ℂ E]
attribute [local instance] Abelian.hasFiniteBiproducts
local instance (i : Fin (rank C)) : Simple (Sᶜ i) := simples_simple C i
local instance (i : Fin (rank C)) : FiniteDimensional ℂ (Sᶜ i ⟶ Sᶜ i) :=
  IsFusionCategory.hom_finite _ _

section
variable {k : Type*} [CommSemiring k] {I J : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
variable {A B F : Type*} [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
  [AddCommMonoid F] [Module k F]

/-- A bilinear contraction with dual bases is natural under any linear map.
This is the matrix identity needed to change fusion bases across a morphism. -/
theorem dualBasis_contraction_natural (a : Module.Basis I k A) (b : Module.Basis J k B)
    (L : A →ₗ[k] B) (f : B →ₗ[k] Module.Dual k A →ₗ[k] F) :
    (∑ i, f (L (a i)) (a.dualBasis i)) =
      ∑ j, f (b j) (Module.Dual.transpose L (b.dualBasis j)) := by
  let c : I → J → k := fun i j => b.repr (L (a i)) j
  have hL (i : I) : L (a i) = ∑ j, c i j • b j := (b.sum_repr _).symm
  have hD (j : J) : Module.Dual.transpose L (b.dualBasis j) =
      ∑ i, c i j • a.dualBasis i := by
    simpa [c, Module.Basis.dualBasis_repr, Module.Dual.transpose_apply] using
      (a.dualBasis.sum_repr (Module.Dual.transpose L (b.dualBasis j))).symm
  simp only [hL, hD, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm
end

set_option backward.isDefEq.respectTransparency false in
/-- Simple projections form the dual basis to simple inclusions. -/
theorem pairing_simpleProjection (V : C.Obj) (i : Fin (rank C))
    (a : Fin (Module.finrank ℂ (Sᶜ i ⟶ V))) :
    simpleHomPairingEquiv (Sᶜ i) V (simpleProjection C V i a) =
      (simpleInclusionBasis C V i).dualBasis a := by
  refine (simpleInclusionBasis C V i).ext fun b => ?_
  rw [Module.Basis.dualBasis_apply_self]
  by_cases h : b = a <;> simp [simpleHomPairingEquiv, simpleHomPairing,
    simpleInclusion, simpleProjection, Category.assoc, h]; rfl

/-- Basis contractions are natural in an arbitrary morphism. -/
theorem simpleBasis_contraction_natural (i : Fin (rank C)) (q : V ⟶ W)
    (F : (Sᶜ i ⟶ W) →ₗ[ℂ] (V ⟶ Sᶜ i) →ₗ[ℂ] E) :
    (∑ a, F (simpleInclusion C V i a ≫ q) (simpleProjection C V i a)) =
      ∑ b, F (simpleInclusion C W i b) (q ≫ simpleProjection C W i b) := by
  let A := simpleInclusionBasis C V i
  let B := simpleInclusionBasis C W i
  let P := simpleHomPairingEquiv (Sᶜ i) V
  let F' : (Sᶜ i ⟶ W) →ₗ[ℂ]
      Module.Dual ℂ (Sᶜ i ⟶ V) →ₗ[ℂ] E :=
    (LinearMap.lcomp ℂ E P.symm.toLinearMap).comp F
  simpa only [F', LinearMap.comp_apply, LinearMap.lcomp_apply, Linear.rightComp_apply,
    LinearEquiv.coe_coe, A, B, P, simpleInclusionBasis_apply,
    ← pairing_simpleProjection, ← simpleHomPairingEquiv_natural, LinearEquiv.symm_apply_apply] using
    dualBasis_contraction_natural A B (Linear.rightComp ℂ (Sᶜ i) q) F'

/-- A mixed crossing block, with the input and output test strands allowed
to differ, is bilinear in its two fusion morphisms. -/
def mixedCrossingBilinear {k : Type*} [CommSemiring k] {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D] (X T U R S : D)
    [HasRightDual R] [HasRightDual S] :
    (R ⟶ U ⊗ S) →ₗ[k] (T ⊗ S ⟶ R) →ₗ[k]
      (((R ⊗ X) ⊗ Rᘁ) ⊗ T ⟶ U ⊗ ((S ⊗ X) ⊗ Sᘁ)) where
  toFun g := {
    toFun := fun f => mixedCrossing X T U g f
    map_add' := by
      intro f f'
      simp [mixedCrossing, closeFusionMap, tensorRightHomEquiv, Category.assoc,
        tensorHom_def, MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
       Preadditive.comp_add, Preadditive.add_comp]
    map_smul' := by
      intro r f
      simp [mixedCrossing, closeFusionMap, tensorRightHomEquiv, Category.assoc,
        tensorHom_def, MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
       Linear.comp_smul, Linear.smul_comp] }
  map_add' := by
    intro g g'
    ext f
    simp [mixedCrossing, Category.assoc, tensorHom_def, MonoidalPreadditive.add_whiskerRight,
      Preadditive.comp_add, Preadditive.add_comp]
  map_smul' := by
    intro r g
    ext f
    simp [mixedCrossing, Category.assoc, tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Linear.comp_smul, Linear.smul_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A finite splitting can be used to refine a simple-basis contraction. -/
theorem simpleBasis_contraction_refinement {J : Type} [Fintype J] {V : J → C.Obj} {W : C.Obj}
    (i : Fin (rank C)) (q : ∀ j, V j ⟶ W) (r : ∀ j, W ⟶ V j)
    (h : (∑ j, r j ≫ q j) = 𝟙 W)
    (F : (Sᶜ i ⟶ W) →ₗ[ℂ] (W ⟶ Sᶜ i) →ₗ[ℂ] E) :
    (∑ j, ∑ a, F (simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection C (V j) i a)) =
      ∑ b, F (simpleInclusion C W i b) (simpleProjection C W i b) := by
  have step (j : J) : (∑ a, F (simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection C (V j) i a)) =
      ∑ b, F (simpleInclusion C W i b) (r j ≫ q j ≫ simpleProjection C W i b) := by
    let F' : (Sᶜ i ⟶ W) →ₗ[ℂ] (V j ⟶ Sᶜ i) →ₗ[ℂ] E :=
      (LinearMap.lcomp ℂ E (Linear.leftComp ℂ (Sᶜ i) (r j))).comp F
    simpa [F', Category.assoc] using simpleBasis_contraction_natural C i (q j) F'
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← map_sum, ← Category.assoc, ← Preadditive.sum_comp, h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Nested fusion decompositions give the direct crossing-block contraction. -/
theorem crossingBlock_refinement (X T U : C.Obj) (i j : Fin (rank C)) :
    (∑ p : simplePieces C (U ⊗ Sᶜ j), ∑ a : crossingIndex C T i p.1,
      nestedCrossingBlock C X T U i p.1 j a p.2) = ∑ b, crossingSummand C X (T ⊗ U) i j b := by
  let J := simplePieces C (U ⊗ Sᶜ j)
  let W := (T ⊗ U) ⊗ Sᶜ j
  let V : J → C.Obj := fun p => T ⊗ Sᶜ p.1
  let q (p : J) : V p ⟶ W := (T ◁ crossingInclusion C U p.1 j p.2) ≫ (α_ T U (Sᶜ j)).inv
  let r (p : J) : W ⟶ V p := (α_ T U (Sᶜ j)).hom ≫ (T ◁ crossingProjection C U p.1 j p.2)
  have h : (∑ p, r p ≫ q p) = 𝟙 W := by
    simp only [r, q, Category.assoc, ← whiskerLeft_comp_assoc,
      ← Preadditive.comp_sum, ← Preadditive.sum_comp, ← whiskerLeft_sum]
    rw [crossing_completeness, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]
  simpa [V, W, J, q, r, nestedCrossingBlock, crossingSummand, simpleProjection,
    crossingInclusion, crossingProjection, mixedCrossingBilinear, mixedCrossing, crossingBlock, Category.assoc] using
    simpleBasis_contraction_refinement C i q r h
      (mixedCrossingBilinear (k := ℂ) X (T ⊗ U) (T ⊗ U) (Sᶜ i) (Sᶜ j))

end PropertyF.Ground.CentreInduction

end

/-! Naturality in the crossed object for the proposed induction crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
-- Chosen simple representatives of the base category.
local notation "Sᶜ" => simples C
attribute [local instance] Abelian.hasFiniteBiproducts

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable {T U R S : D}

section
variable [HasRightDual S] [HasRightDual R]

set_option backward.isDefEq.respectTransparency false in
/-- The closed fusion map is characterized by its evaluation pairing. -/
theorem closeFusionMap_evaluation (f : T ⊗ S ⟶ R) :
    (closeFusionMap T S f ▷ S) ≫ ε_ S (Sᘁ) =
      𝟙 _ ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ) := by
  apply (tensorRightHomEquiv (Rᘁ ⊗ T) S Sᘁ (𝟙_ D)).injective
  rw [tensorRightHomEquiv_whiskerRight_comp_evaluation]
  have hc : 𝟙 ((Rᘁ ⊗ T) ⊗ S) ⊗≫ (Rᘁ ◁ f) ⊗≫ ε_ R Rᘁ =
      (α_ Rᘁ T S).hom ≫ (Rᘁ ◁ f) ≫ ε_ R Rᘁ := by monoidal
  rw [hc]
  simp [closeFusionMap]


set_option backward.isDefEq.respectTransparency false in
/-- Closing a fusion map is natural in its test strand. -/
theorem closeFusionMap_pre_test (h : T ⟶ U) (f : U ⊗ S ⟶ R) :
    (Rᘁ ◁ h) ≫ closeFusionMap U S f =
      closeFusionMap T S ((h ▷ S) ≫ f) :=
  Dimensions.evaluation_ext (X := S) <| by
    simp only [comp_whiskerRight, Category.assoc, closeFusionMap_evaluation, whiskerLeft_comp]
    monoidal

variable (X : D)

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the output of a crossing block composes the
fusion inclusion with that map. -/
@[reassoc]
theorem crossingBlock_post_test (h : T ⟶ U)
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    crossingBlock X T S g f ≫ (h ▷ ((S ⊗ X) ⊗ Sᘁ)) =
      mixedCrossing X T U (g ≫ (h ▷ S)) f := by
  dsimp only [crossingBlock, mixedCrossing]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the input of a crossing block composes the
fusion projection with that map. -/
@[reassoc]
theorem crossingBlock_pre_test (h : T ⟶ U)
    (g : R ⟶ U ⊗ S) (f : U ⊗ S ⟶ R) :
    (((R ⊗ X) ⊗ Rᘁ) ◁ h) ≫ crossingBlock X U S g f =
      mixedCrossing X T U g ((h ▷ S) ≫ f) := by
  simp only [crossingBlock, mixedCrossing, tensorHom_def, Category.assoc]
  rw [associator_naturality_right_assoc, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    closeFusionMap_pre_test, whisker_exchange_assoc]
end

variable (X : C.Obj)

/-- Summing the crossing blocks removes the dependence on the chosen fusion
basis, so a map of test objects can pass through each matrix entry. -/
theorem crossingBlock_sum_natural_test
    (T U : C.Obj) (h : T ⟶ U) (i j : Fin (rank C)) :
    (∑ b, (((Sᶜ i ⊗ X) ⊗ (Sᶜ i)ᘁ) ◁ h) ≫ crossingSummand C X U i j b) =
    ∑ a, crossingSummand C X T i j a ≫ (h ▷ ((Sᶜ j ⊗ X) ⊗ (Sᶜ j)ᘁ)) := by
  simpa only [crossingSummand, crossingBlock_pre_test, crossingBlock_post_test,
    mixedCrossingBilinear, LinearMap.coe_mk, AddHom.coe_mk, crossingInclusion, crossingProjection, simpleProjection] using
    (simpleBasis_contraction_natural C i (h ▷ Sᶜ j)
      (mixedCrossingBilinear (k := ℂ) X T U (Sᶜ i) (Sᶜ j))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The proposed induction crossing is natural in the crossed object. -/
theorem crossingCandidate_natural_test {T U : C.Obj} (h : T ⟶ U) :
    (underlying C X ◁ h) ≫ crossingCandidate C X U =
      crossingCandidate C X T ≫ (h ▷ underlying C X) := by
  refine rightDistributor_ext_left (f := inductionSummand C X) fun i => ?_
  dsimp [underlying] at *
  rw [← whisker_exchange_assoc]
  simp only [crossingCandidate_on_summand, crossingCandidate_on_summand_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa only [Category.assoc, whisker_exchange, Preadditive.sum_comp] using
    congrArg (fun g => g ≫ (U ◁ biproduct.ι (inductionSummand C X) j))
      (crossingBlock_sum_natural_test C X T U h i j)

end PropertyF.Ground.CentreInduction
