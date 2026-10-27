module
public import PropertyF.Ground.Fusion.Agreement

/-! Compatibility with the earlier conditional formulation. The construction
below is not needed in the final target's dependency cone. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace PropertyF.Ground

/-- Construct all fields of the earlier `FusionData` from the genuine target
category, including the positive FP character. -/
def fusionData (D : BraidedFusionCategory) : PropertyF.FusionData D.Obj where
  rank := rank D
  simpleObject := simples D
  simple_is_simple := simples_simple D
  simple_injective := simples_injective D
  unitIndex := unitIndex D
  unit_iso := Classical.choice (unitIndex_iso D)
  hom_finite := IsFusionCategory.hom_finite
  decomposition := simples_decompose D
  fpSimple := fpSimple D
  fp_positive := fpSimple_pos D
  fp_unit := fpSimple_unit D
  fp_character := fpSimple_mul D

theorem fusionData_globalFPDimension (D : BraidedFusionCategory) :
    (fusionData D).globalFPDimension = globalFPDimension D := rfl

end PropertyF.Ground
