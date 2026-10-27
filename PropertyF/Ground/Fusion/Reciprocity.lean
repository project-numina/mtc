module
public import PropertyF.Ground.Fusion.Multiplicity

/-! Frobenius reciprocity for actual categorical Hom spaces. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace PropertyF.Ground
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Rigidity's Hom equivalence is complex-linear. -/
def tensorRightHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z ⊗ Y') where
  toEquiv := tensorRightHomEquiv X Y Y' Z
  map_add' f g := by simp [tensorRightHomEquiv]
  map_smul' c f := by simp [tensorRightHomEquiv]

/-- Frobenius reciprocity for Hom dimensions. -/
theorem finrank_frobenius_reciprocity [RigidCategory C] (X Y Z : C) :
    Module.finrank ℂ (Z ⟶ X ⊗ Y) = Module.finrank ℂ (Z ⊗ (ᘁY) ⟶ X) :=
  (tensorRightHomLinearEquiv Z (ᘁY) Y X).finrank_eq.symm

/-- Fusion reciprocity with the dual kept as an actual object. -/
theorem fusionCoeff_reciprocity (D : BraidedFusionCategory.{v,u})
    (i j k : Fin (rank D)) :
    fusionCoeff D i j k =
      Module.finrank ℂ (simples D i ⟶ simples D k ⊗ (ᘁ(simples D j))) := by
  calc
    _ = Module.finrank ℂ (simples D k ⊗ (ᘁ(simples D j)) ⟶ simples D i) :=
      finrank_frobenius_reciprocity (simples D i) (simples D j) (simples D k)
    _ = _ := finrank_to_simple_eq_from_simple D _ i

end PropertyF.Ground
