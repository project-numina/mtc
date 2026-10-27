module
public import PropertyF.Ground.Integrate.LegacyBridge
public import PropertyF.Main

/-! Conditional compatibility with the old proof. This does not prove the
unconditional target: `StandardInputs` is an explicit unconstructed premise,
and this theorem is forbidden in the strict final dependency cone. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- The previous conditional theorem applies to the frozen ground statement
once the explicitly named standard inputs are supplied. -/
theorem target_of_legacy_standardInputs (H : PropertyF.StandardInputs.{v,u}) :
    TargetStatement.{v,u} := by
  intro C hPU hF
  have h := PropertyF.propertyF_implies_weaklyIntegral H (legacyCategory C)
    (legacy_hasPseudoUnitaryGaloisConjugate C hPU) hF
  simpa only [legacy_globalFPDimension_eq] using h

end PropertyF.Ground
