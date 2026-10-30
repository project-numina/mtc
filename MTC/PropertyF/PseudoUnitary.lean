module
public import MTC.PropertyF.Theorem

open MTC.Fusion

open MTC.Braided

/-! # Property F with a pseudo-unitary conjugate

These are direct consequences of `MTC.PropertyF.weaklyIntegral_of_propertyF`. The identity
Galois conjugate gives the pseudo-unitary special case.
-/

@[expose] public noncomputable section
open CategoryTheory MTC MTC
namespace MTC.PropertyF
universe v u

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
  weaklyIntegral_of_propertyF C
    (hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary C h) hF

end MTC.PropertyF
