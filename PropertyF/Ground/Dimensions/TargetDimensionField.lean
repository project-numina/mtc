module
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Ground.Fusion.SpectralIntegral

@[expose] public noncomputable section
namespace PropertyF.Ground.Dimensions
universe v u

/-- The target global FP dimension has the field-theoretic package used by
the original conditional theorem. Its integrality is proved from fusion
matrices, not assumed in the category. -/
def dimensionFieldOfGround (C : Ground.BraidedFusionCategory.{v,u}) :
    DimensionField (Ground.globalFPDimension C) :=
  dimensionFieldOfIntegral _ (by
    simpa using ((Ground.globalFPDimension_isIntegral C).algebraMap (B := ℂ)))

end PropertyF.Ground.Dimensions
