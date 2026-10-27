module
public import PropertyF.Ground.Integrate.Conjugacy
public import PropertyF.Ground.Modular.FusionTransport

/-! Transport property F across the target's semilinear braided equivalence. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- A braided equivalence carries property F to the conjugate category. -/
theorem galois_propertyF {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ}
    (E : GaloisConjugate C D σ) (hF : HasPropertyF C.Obj) : HasPropertyF D.Obj :=
  Modular.conjugate_propertyF C D E hF

end PropertyF.Ground
