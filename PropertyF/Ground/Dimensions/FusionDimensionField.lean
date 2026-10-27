module
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Ground.Fusion.Integrality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [Abelian C] [Linear ℂ C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- For the existing fusion-character interface, `DimensionField` is now
constructed rather than assumed. This compatibility result does not establish
the character from the ground category interface. -/
def dimensionFieldOfFusionData (F : FusionData C) : DimensionField F.globalFPDimension :=
  dimensionFieldOfIntegral _ (by
    simpa using (F.globalFPDimension_isIntegral.algebraMap (B := ℂ)))

end PropertyF.Ground.Dimensions
