module
public import PropertyF.Ground.Target

/-! Elementary consistency checks for the frozen conjugacy condition. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- Identity gives a genuine semilinear braided equivalence. -/
def GaloisConjugate.refl (C : BraidedFusionCategory.{v,u}) :
    GaloisConjugate C C (RingEquiv.refl ℂ) where
  equivalence := CategoryTheory.Equivalence.refl
  monoidal := inferInstanceAs ((𝟭 C.Obj).Monoidal)
  braided := inferInstanceAs ((𝟭 C.Obj).Braided)
  map_smul := by intros; rfl

/-- Pseudo-unitary categories satisfy the conjugate condition themselves. -/
theorem hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary
    (C : BraidedFusionCategory.{v,u}) (h : PseudoUnitary C) :
    HasPseudoUnitaryGaloisConjugate C :=
  ⟨C, RingEquiv.refl ℂ, ⟨GaloisConjugate.refl C⟩, h⟩

end PropertyF.Ground
