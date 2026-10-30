module
public import MTC.PropertyF.Theorem

/-! # Property F with a pseudo-unitary conjugate

These are direct consequences of `MTC.target`. The identity
Galois conjugate gives the pseudo-unitary special case.
-/

@[expose] public noncomputable section
open CategoryTheory MTC MTC
namespace MTC.PropertyF
universe v u

/-- Property F implies weak integrality when a pseudo-unitary conjugate exists. -/
theorem weaklyIntegral_of_propertyF_of_conjugate (C : BraidedFusionCategory.{v,u})
    (h : HasPseudoUnitaryGaloisConjugate C) (hF : HasPropertyF C.Obj) :
    WeaklyIntegral (globalFPDimension C) :=
  MTC.target C h hF

/-- A pseudo-unitary category is its own pseudo-unitary Galois conjugate. -/
theorem hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary
    (C : BraidedFusionCategory.{v,u}) (h : PseudoUnitary C) :
    HasPseudoUnitaryGaloisConjugate C := by
  refine ⟨C, RingEquiv.refl ℂ, ⟨?_, h⟩⟩
  let E : C.Obj ≌ C.Obj := CategoryTheory.Equivalence.refl
  let : E.functor.Braided := by
    change (𝟭 C.Obj).Braided
    infer_instance
  exact ⟨{ equivalence := E, map_smul := by intros; rfl }⟩

/-- In a pseudo-unitary braided fusion category, property F implies weak integrality. -/
theorem weaklyIntegral_of_propertyF_of_pseudoUnitary (C : BraidedFusionCategory.{v,u})
    (h : PseudoUnitary C) (hF : HasPropertyF C.Obj) :
    WeaklyIntegral (globalFPDimension C) :=
  weaklyIntegral_of_propertyF_of_conjugate C
    (hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary C h) hF

end MTC.PropertyF
