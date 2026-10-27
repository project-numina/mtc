module
public import PropertyF.Ground.Integrate.Conjugacy
public import PropertyF.Ground.Modular.BraidFunctor

/-! Transport property F across the target's semilinear braided equivalence. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- A braided equivalence carries property F to the conjugate category. -/
theorem galois_propertyF {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ}
    (E : GaloisConjugate C D σ) (hF : HasPropertyF C.Obj) : HasPropertyF D.Obj := by
  let _ := E.braided
  intro Y n
  obtain ⟨X, ⟨e⟩⟩ := Modular.braidImages_of_essentiallySurjective E.equivalence.functor Y n
  have _ : Finite (braidImage X n) := hF X n
  exact Finite.of_equiv (braidImage X n) e.toEquiv.symm

end PropertyF.Ground
