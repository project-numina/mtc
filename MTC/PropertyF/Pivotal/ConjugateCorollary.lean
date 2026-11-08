module
public import MTC.PropertyF.Pivotal.GaloisDimensionTransport
public import MTC.PropertyF.Theorem

/-! # Property F with a pseudo-unitary Galois conjugate

The original checked property-F theorem supplies weak integrality. Semilinear
transport of intrinsic global dimension then gives pseudo-unitarity of the
original category, proving the manuscript's full corollary.
-/

@[expose] public noncomputable section
open MTC.Fusion MTC.Braided
namespace MTC.PropertyF.Pivotal
universe v u

/-- A braided fusion category with property F and a pseudo-unitary Galois
conjugate is pseudo-unitary and weakly integral. -/
theorem pseudoUnitary_and_weaklyIntegral_of_propertyF_of_conjugate
    (C : BraidedFusionCategory.{v,u})
    (hconj : HasPseudoUnitaryGaloisConjugate C) (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ WeaklyIntegral (globalFPDimension C) := by
  have hw : WeaklyIntegral (globalFPDimension C) :=
    MTC.PropertyF.weaklyIntegral_of_propertyF C hconj hF
  obtain ⟨D, σ, ⟨h⟩, hD⟩ := hconj
  obtain ⟨z, hz⟩ := hw
  have hfix : σ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ) := by
    rw [hz]
    exact map_intCast σ z
  constructor
  · change globalDimension C = (globalFPDimension C : ℂ)
    apply σ.injective
    calc
      σ (globalDimension C) = globalDimension D := (globalDimension_galois h).symm
      _ = (globalFPDimension D : ℂ) := hD
      _ = (globalFPDimension C : ℂ) := by rw [MTC.Modular.conjugate_globalFPDimension h]
      _ = σ (globalFPDimension C : ℂ) := hfix.symm
  · exact ⟨z, hz⟩

/-- A pseudo-unitary weakly integral fusion category has pseudo-unitary
Galois conjugates in every semilinearly equivalent presentation. -/
theorem allGaloisConjugatesPseudoUnitary_of_pseudoUnitary_of_weaklyIntegral
    (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C)
    (hw : WeaklyIntegral (globalFPDimension C)) :
    AllGaloisConjugatesPseudoUnitary C := by
  obtain ⟨z, hz⟩ := hw
  intro D σ h
  obtain ⟨h⟩ := h
  change globalDimension D = (globalFPDimension D : ℂ)
  have hfix : σ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ) := by
    rw [hz]
    exact map_intCast σ z
  rw [globalDimension_galois h, hpu, hfix, MTC.Modular.conjugate_globalFPDimension h]

/-- Under the corollary's hypothesis, all represented Galois conjugates are
pseudo-unitary as well. -/
theorem allGaloisConjugatesPseudoUnitary_of_propertyF_of_conjugate
    (C : BraidedFusionCategory.{v,u})
    (hconj : HasPseudoUnitaryGaloisConjugate C) (hF : HasPropertyF C.Obj) :
    AllGaloisConjugatesPseudoUnitary C := by
  obtain ⟨hpu, hw⟩ := pseudoUnitary_and_weaklyIntegral_of_propertyF_of_conjugate C hconj hF
  exact allGaloisConjugatesPseudoUnitary_of_pseudoUnitary_of_weaklyIntegral C hpu hw

/-- The manuscript's pseudo-unitary-conjugate corollary holds as stated. -/
theorem pseudoUnitaryConjugateStatement_proved : PseudoUnitaryConjugateStatement := by
  intro C hconj hF
  exact pseudoUnitary_and_weaklyIntegral_of_propertyF_of_conjugate C hconj hF

end MTC.PropertyF.Pivotal
end
