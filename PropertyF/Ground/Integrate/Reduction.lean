module
public import PropertyF.Ground.Integrate.Arithmetic
public import PropertyF.Ground.Integrate.PropertyFTransport

/-! Bundle-free reduction of the target to FP invariance under conjugacy and the
paper's Galois-fixedness argument for pseudo-unitary categories. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- The two remaining categorical obligations suffice to prove the frozen target.
This is a reduction with explicitly displayed premises, not the target theorem. -/
theorem target_of_galois_invariance_and_pseudo_fixedness
    (hInvariant : ∀ {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ},
      GaloisConjugate C D σ → globalFPDimension C = globalFPDimension D)
    (hFixed : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      σ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ)) :
    TargetStatement.{v,u} := by
  intro C hPU hF
  obtain ⟨D, σ, ⟨E⟩, hD⟩ := hPU
  have hDF : HasPropertyF D.Obj := galois_propertyF E hF
  have hDInt := weaklyIntegral_of_globalFPDimension_fixed D (hFixed D hD hDF)
  rwa [hInvariant E]

end PropertyF.Ground
