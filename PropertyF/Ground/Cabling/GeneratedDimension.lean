module
public import PropertyF.Ground.Cabling.GeneratedFusion
public import PropertyF.Ground.Fusion.SubcategoryDimension
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

instance (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    (generatedFusionInclusion D X).Additive := by
  change (generatedInclusion X).Additive
  infer_instance
instance (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    (generatedFusionInclusion D X).Linear ℂ := by
  change (generatedInclusion X).Linear ℂ
  infer_instance

/-- The inclusion preserves the FP dimension of each object. -/
theorem generatedFusionInclusion_fpDimension (D : Ground.BraidedFusionCategory.{v,u})
    (X : D.Obj) (Y : (generatedFusion D X).Obj) :
    Ground.fpDimension D ((generatedFusionInclusion D X).obj Y) =
      Ground.fpDimension (generatedFusion D X) Y :=
  Ground.fpDimension_functor (generatedFusion D X) D (generatedFusionInclusion D X) Y

/-- The generated fusion subcategory has no larger global FP dimension. -/
theorem generatedFusion_globalFPDimension_le (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    Ground.globalFPDimension (generatedFusion D X) ≤ Ground.globalFPDimension D :=
  Ground.globalFPDimension_le_of_full_functor (generatedFusion D X) D (generatedFusionInclusion D X)
end PropertyF.Ground.Cabling
