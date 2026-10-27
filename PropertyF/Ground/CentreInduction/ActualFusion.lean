module
public import PropertyF.Ground.CentreInduction.UnitCentrality
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion
public import PropertyF.Ground.Fusion.SpectralIntegral

/-! Centre fusion and FP dimension using the constructed induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u

/-- If the actual centre already has a fusion structure, its global FP
 dimension is the square of the base global FP dimension. -/
theorem globalFPDimension_square_of_actual_induction (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)] :
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 :=
  globalFPDimension_square_of_adjunction C (induction C) (actualAdjunction C)
    (fun _ => ⟨Iso.refl _⟩)




end PropertyF.Ground.CentreInduction
