module
public import MTC.Center.Induction.CrossingBlocks
public import MTC.CategoryTheory.Dimensions.DualTensorNaturality

open PropertyF.Ground.Dimensions Algebra

/-! Dual bases for the actual fusion summand inclusions and projections. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable {C : BraidedFusionCategory.{v,u}}
-- Chosen simple representatives of the base category.
local notation "Sᶜ" => simples C
variable {V W : C.Obj} {E : Type*} [AddCommGroup E] [Module ℂ E]
attribute [local instance] Abelian.hasFiniteBiproducts IsFusionCategory.hom_finite
local instance (i : Fin (rank C)) : Simple (Sᶜ i) := simples_simple C i


set_option backward.isDefEq.respectTransparency false in
/-- Simple projections form the dual basis to simple inclusions. -/
theorem pairing_simpleProjection {V : C.Obj} {i : Fin (rank C)}
    (a : Fin (Module.finrank ℂ (Sᶜ i ⟶ V))) :
    simpleHomPairingEquiv (Sᶜ i) V (simpleProjection V i a) =
      (simpleInclusionBasis C V i).dualBasis a :=
  LinearMap.ext fun g => (simpleEndScalar (k := ℂ) (Sᶜ i)).symm.injective <| End.ext <| by
    simpa [Module.Basis.dualBasis_apply, simpleHomPairingEquiv, simpleHomPairing, simpleProjection,
      simpleEndScalar, algebraMap_eq_smul_one] using (simpleInclusionBasis_projection g a).symm

/-- Basis contractions are natural in an arbitrary morphism. -/
theorem simpleBasis_contraction_natural {i : Fin (rank C)} (q : V ⟶ W)
    (F : (Sᶜ i ⟶ W) →ₗ[ℂ] (V ⟶ Sᶜ i) →ₗ[ℂ] E) :
    (∑ a, F (simpleInclusion C V i a ≫ q) (simpleProjection V i a)) =
      ∑ b, F (simpleInclusion C W i b) (q ≫ simpleProjection W i b) := by
  simpa [simpleInclusionBasis_apply, ← pairing_simpleProjection,
    ← simpleHomPairingEquiv_natural] using
    dualBasis_contraction_natural (simpleInclusionBasis C V i) (simpleInclusionBasis C W i)
      (Linear.rightComp ℂ (Sᶜ i) q)
      ((LinearMap.lcomp ℂ E (simpleHomPairingEquiv (Sᶜ i) V).symm.toLinearMap).comp F)

/-- A mixed crossing block, with the input and output test strands allowed
to differ, is bilinear in its two fusion morphisms. -/
def mixedCrossingBilinear {k : Type*} [CommSemiring k] {D : Type u}
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D] (X T U R S : D)
    [HasRightDual R] [HasRightDual S] :
    (R ⟶ U ⊗ S) →ₗ[k] (T ⊗ S ⟶ R) →ₗ[k]
      (conjugate R X ⊗ T ⟶ U ⊗ conjugate S X) where
  toFun g := {
    toFun := fun f => mixedCrossing X T U g f
    map_add' := by
      intro f f'
      simp [mixedCrossing, closeFusionMap, tensorRightHomEquiv, tensorHom_def]
    map_smul' := by
      intro r f
      simp [mixedCrossing, closeFusionMap, tensorRightHomEquiv, tensorHom_def] }
  map_add' := by
    intro g g'
    ext f
    simp [mixedCrossing, tensorHom_def]
  map_smul' := by
    intro r g
    ext f
    simp [mixedCrossing, tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- A finite splitting can be used to refine a simple-basis contraction. -/
theorem simpleBasis_contraction_refinement {J : Type} [Fintype J] {V : J → C.Obj} {W : C.Obj}
    {i : Fin (rank C)} (q : ∀ j, V j ⟶ W) (r : ∀ j, W ⟶ V j)
    (h : (∑ j, r j ≫ q j) = 𝟙 W)
    (F : (Sᶜ i ⟶ W) →ₗ[ℂ] (W ⟶ Sᶜ i) →ₗ[ℂ] E) :
    (∑ j, ∑ a, F (simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection (V j) i a)) =
      ∑ b, F (simpleInclusion C W i b) (simpleProjection W i b) := by
  have step (j : J) : (∑ a, F (simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection (V j) i a)) =
      ∑ b, F (simpleInclusion C W i b) (r j ≫ q j ≫ simpleProjection W i b) := by
    simpa using simpleBasis_contraction_natural (q j)
      ((LinearMap.lcomp ℂ E (Linear.leftComp ℂ (Sᶜ i) (r j))).comp F)
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← map_sum, ← Category.assoc, ← Preadditive.sum_comp, h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Nested fusion decompositions give the direct crossing-block contraction. -/
theorem crossingBlock_refinement (X T U : C.Obj) (i j : Fin (rank C)) :
    (∑ p : simplePieces C (U ⊗ Sᶜ j), ∑ a : crossingIndex T i p.1,
      nestedCrossingBlock X T U i p.1 j a p.2) = ∑ b, crossingSummand X (T ⊗ U) i j b := by
  let J := simplePieces C (U ⊗ Sᶜ j)
  let q (p : J) := (T ◁ crossingInclusion U p.1 j p.2) ≫ (α_ T U (Sᶜ j)).inv
  let r (p : J) := (α_ T U (Sᶜ j)).hom ≫ (T ◁ crossingProjection U p.1 j p.2)
  have h : (∑ p, r p ≫ q p) = 𝟙 ((T ⊗ U) ⊗ Sᶜ j) := by
    simp [r, q, J, ← whiskerLeft_comp_assoc, ← Preadditive.comp_sum,
      ← Preadditive.sum_comp, ← whiskerLeft_sum, crossingProjection, crossingInclusion,
      simple_completeness, -whiskerLeft_comp]
  simpa [J, q, r, nestedCrossingBlock, crossingSummand, simpleProjection, crossingInclusion,
    crossingProjection, mixedCrossingBilinear, crossingBlock, Category.assoc] using
    simpleBasis_contraction_refinement q r h
      (mixedCrossingBilinear (k := ℂ) X (T ⊗ U) (T ⊗ U) (Sᶜ i) (Sᶜ j))

end PropertyF.Ground.CentreInduction

end

/-! Naturality in the crossed object for the proposed induction crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable {C : BraidedFusionCategory.{v,u}}
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
      𝟙 _ ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ) :=
  (tensorRightHomEquiv (Rᘁ ⊗ T) S Sᘁ (𝟙_ D)).injective <| by
    rw [tensorRightHomEquiv_whiskerRight_comp_evaluation]
    simp [closeFusionMap, monoidalComp]


set_option backward.isDefEq.respectTransparency false in
/-- Closing a fusion map is natural in its test strand. -/
theorem closeFusionMap_pre_test (h : T ⟶ U) (f : U ⊗ S ⟶ R) :
    (Rᘁ ◁ h) ≫ closeFusionMap U S f =
      closeFusionMap T S ((h ▷ S) ≫ f) :=
  Dimensions.evaluation_ext (X := S) <| by
    simp [comp_whiskerRight, closeFusionMap_evaluation, whiskerLeft_comp, monoidalComp]

variable (X : D) (h : T ⟶ U)

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the output of a crossing block composes the
fusion inclusion with that map. -/
theorem crossingBlock_post_test (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    crossingBlock X T S g f ≫ (h ▷ conjugate S X) =
      mixedCrossing X T U (g ≫ (h ▷ S)) f := by
  dsimp only [crossingBlock, mixedCrossing]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the input of a crossing block composes the
fusion projection with that map. -/
theorem crossingBlock_pre_test (g : R ⟶ U ⊗ S) (f : U ⊗ S ⟶ R) :
    (conjugate R X ◁ h) ≫ crossingBlock X U S g f =
      mixedCrossing X T U g ((h ▷ S) ≫ f) := by
  simp only [crossingBlock, mixedCrossing, tensorHom_def, Category.assoc]
  rw [associator_naturality_right_assoc, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    closeFusionMap_pre_test, whisker_exchange_assoc]
end

variable (X : C.Obj)
-- The induction crossing on the fixed middle object.
local notation "βᶜ" => crossingCandidate X
local notation "Vᶜ" => inductionSummand X

/-- Summing the crossing blocks removes the dependence on the chosen fusion
basis, so a map of test objects can pass through each matrix entry. -/
theorem crossingBlock_sum_natural_test
    (T U : C.Obj) (h : T ⟶ U) (i j : Fin (rank C)) :
    (∑ b, (Vᶜ i ◁ h) ≫ crossingSummand X U i j b) =
    ∑ a, crossingSummand X T i j a ≫ (h ▷ Vᶜ j) := by
  simpa only [crossingSummand, crossingBlock_pre_test, crossingBlock_post_test,
    mixedCrossingBilinear, LinearMap.coe_mk, AddHom.coe_mk, crossingInclusion,
    crossingProjection, simpleProjection] using
    (simpleBasis_contraction_natural (h ▷ Sᶜ j)
      (mixedCrossingBilinear (k := ℂ) X T U (Sᶜ i) (Sᶜ j))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The proposed induction crossing is natural in the crossed object. -/
theorem crossingCandidate_natural_test {T U : C.Obj} (h : T ⟶ U) :
    (underlying X ◁ h) ≫ βᶜ U = βᶜ T ≫ (h ▷ underlying X) :=
  rightDistributor_ext_left (f := inductionSummand X) fun i => by
    dsimp [underlying] at *
    rw [← whisker_exchange_assoc]
    simp only [crossingCandidate_on_summand, crossingCandidate_on_summand_assoc,
      Preadditive.comp_sum, Preadditive.sum_comp]
    simp_rw [Category.assoc, whisker_exchange, ← Category.assoc, ← Preadditive.sum_comp,
      crossingBlock_sum_natural_test X T U h i, ← Preadditive.sum_comp]

end PropertyF.Ground.CentreInduction
