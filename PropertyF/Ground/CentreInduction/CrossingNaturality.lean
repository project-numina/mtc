module
public import PropertyF.Ground.CentreInduction.BasisPairing
public import PropertyF.Ground.Dimensions.DualTensorNaturality

/-! Naturality in the crossed object for the proposed induction crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- Closing a fusion map is natural in its test strand. -/
theorem closeFusionMap_pre_test {T U R S : D} (h : T ⟶ U) (f : U ⊗ S ⟶ R) :
    (Rᘁ ◁ h) ≫ closeFusionMap U S R f =
      closeFusionMap T S R ((h ▷ S) ≫ f) := by
  simp only [closeFusionMap, Category.assoc, comp_rightAdjointMate, comp_whiskerRight]
  rw [whisker_exchange_assoc]
  have hn := Dimensions.rightDualTensorIso_natural h (𝟙 S)
  simp only [tensorHom_id, rightAdjointMate_id, id_tensorHom] at hn
  have hn' := congrArg (fun k => k ▷ T) hn
  have hn'' := reassoc_of% hn'
  simp only [comp_whiskerRight, Category.assoc] at hn''
  rw [hn'']
  rw [whisker_exchange_assoc, associator_naturality_right_assoc]
  rw [associator_naturality_middle_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [rightAdjointMate_comp_evaluation]

variable {k : Type*} [CommSemiring k] [Preadditive D] [Linear k D]
  [MonoidalPreadditive D] [MonoidalLinear k D]

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the output of a crossing block composes the
fusion inclusion with that map. -/
@[reassoc]
theorem crossingBlock_post_test (X : D) {T U R S : D} (h : T ⟶ U)
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    crossingBlock X T R S g f ≫ (h ▷ ((S ⊗ X) ⊗ Sᘁ)) =
      mixedCrossingBilinear (k := k) X T U R S (g ≫ (h ▷ S)) f := by
  simp only [crossingBlock, mixedCrossingBilinear, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the input of a crossing block composes the
fusion projection with that map. -/
@[reassoc]
theorem crossingBlock_pre_test (X : D) {T U R S : D} (h : T ⟶ U)
    (g : R ⟶ U ⊗ S) (f : U ⊗ S ⟶ R) :
    (((R ⊗ X) ⊗ Rᘁ) ◁ h) ≫ crossingBlock X U R S g f =
      mixedCrossingBilinear (k := k) X T U R S g ((h ▷ S) ≫ f) := by
  simp only [crossingBlock, mixedCrossingBilinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [associator_naturality_right_assoc]
  simp only [tensorHom_def, Category.assoc]
  rw [← whisker_exchange_assoc, ← whiskerLeft_comp_assoc, closeFusionMap_pre_test]
  rw [whisker_exchange_assoc]

/-- Summing the crossing blocks removes the dependence on the chosen fusion
basis, so a map of test objects can pass through each matrix entry. -/
theorem crossingBlock_sum_natural_test
    (X T U : C.Obj) (h : T ⟶ U) (i j : Fin (rank C)) :
    (∑ b, (((simples C i ⊗ X) ⊗ (simples C i)ᘁ) ◁ h) ≫
      crossingBlock X U (simples C i) (simples C j)
        (crossingInclusion C U i j b) (crossingProjection C U i j b)) =
    ∑ a, crossingBlock X T (simples C i) (simples C j)
      (crossingInclusion C T i j a) (crossingProjection C T i j a) ≫
        (h ▷ ((simples C j ⊗ X) ⊗ (simples C j)ᘁ)) := by
  simp_rw [crossingBlock_pre_test (k := ℂ), crossingBlock_post_test (k := ℂ)]
  exact (fusionBasis_contraction_natural C i j (h ▷ simples C j)
    (mixedCrossingBilinear (k := ℂ) X T U (simples C i) (simples C j))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The proposed induction crossing is natural in the crossed object. -/
theorem crossingCandidate_natural_test
    (X : C.Obj) {T U : C.Obj} (h : T ⟶ U) :
    (underlying C X ◁ h) ≫ crossingCandidate C X U =
      crossingCandidate C X T ≫ (h ▷ underlying C X) := by
  classical
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  apply (cancel_epi (rightDistributor V T).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  dsimp [V, underlying] at *
  rw [← whisker_exchange_assoc]
  simp only [crossingCandidate_on_summand, crossingCandidate_on_summand_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Category.assoc, whisker_exchange]
  simpa only [Category.assoc, Preadditive.sum_comp, V] using congrArg (fun g => g ≫ (U ◁ biproduct.ι V j))
    (crossingBlock_sum_natural_test C X T U h i j)

end PropertyF.Ground.CentreInduction
