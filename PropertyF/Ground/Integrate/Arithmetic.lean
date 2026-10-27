module
public import PropertyF.Ground.Fusion.SpectralIntegral
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Arithmetic

/-! The final arithmetic descent for the frozen target, without a dimension
field or standard-input hypothesis. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- Once every complex automorphism fixes the global FP dimension, its
algebraic integrality forces it to be an integer. All normal-field and
extension data are constructed, not assumed. -/
theorem weaklyIntegral_of_globalFPDimension_fixed (C : BraidedFusionCategory.{v,u})
    (hfixed : ∀ τ : ℂ ≃+* ℂ,
      τ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ)) :
    WeaklyIntegral (globalFPDimension C) := by
  let δ := globalFPDimension C
  have hδ : IsIntegral ℤ (δ : ℂ) :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ)).mpr
      (globalFPDimension_isIntegral C)
  let K := Dimensions.dimensionNormalField (δ : ℂ)
  have h := Dimensions.finite_galois_normal_field (δ : ℂ) (hδ.tower_top (A := ℚ))
  let : FiniteDimensional ℚ K := h.2.1
  let : IsGalois ℚ K := h.2.2
  let x : K := ⟨(δ : ℂ), h.1⟩
  have hx : IsIntegral ℤ x :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ)).mp (by simpa [x] using hδ)
  have hxfix : ∀ σ : K ≃ₐ[ℚ] K, σ x = x := by
    intro σ
    obtain ⟨τ, hτ⟩ := Dimensions.extend_complex_automorphism K.toSubfield σ.toRingEquiv
    apply Subtype.ext
    calc
      (σ x : ℂ) = τ (x : ℂ) := (hτ x).symm
      _ = (x : ℂ) := hfixed τ
  obtain ⟨z, hz⟩ := integer_of_galois_fixed hx hxfix
  refine ⟨z, ?_⟩
  have hz' := congrArg (fun y : K => (y : ℂ)) hz
  simpa [x, δ] using congrArg Complex.re hz'

end PropertyF.Ground
