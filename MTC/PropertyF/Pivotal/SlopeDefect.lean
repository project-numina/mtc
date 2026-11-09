module
public import MTC.Center.Induction.DrinfeldTheorem
public import MTC.CategoryTheory.Dimensions.MultiplicityDefect
public import MTC.CategoryTheory.Dimensions.DimensionCharacter

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! The actual fourth-dual tensor law makes all root tensor defects involutions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Pivotal
universe v u

variable (C : BraidedFusionCategory.{v,u})

/-- The chosen natural fourth-dual root has an involutive tensor defect,
for arbitrary objects of a braided fusion category. -/
theorem rootTensorDefect_involutive (X Y : C.Obj) :
    IsInvolutiveHom (rootTensorDefect C X Y).hom := by
  apply rootTensorDefect_involution_of_tensor_square
  rw [rootTensor_square_eq_fourthDual_tensor]
  exact (MTC.Center.Induction.fourthDualIso_tensor X Y).symm

/-- The induced operator on every simple fusion multiplicity space is involutive. -/
theorem multiplicityDefect_involutive (i j k : Fin (rank C)) :
    IsInvolutiveElem (multiplicityDefect C i j k).toLinearMap := by
  apply multiplicityDefect_involution_of_tensor_square C k
  rw [rootTensor_square_eq_fourthDual_tensor]
  exact (MTC.Center.Induction.fourthDualIso_tensor (simples C i) (simples C j)).symm

/-- The phase of the pivotal dimension of a simple object has unit norm. -/
theorem norm_pivotalDimension_phase (p : PivotalStructure (C := C.Obj))
    (X : C.Obj) [Simple X] :
    ‖pivotalDimension C p X / (‖pivotalDimension C p X‖ : ℂ)‖ = 1 := by
  have hd : pivotalDimension C p X ≠ 0 := MTC.Modular.unitScalar_rightTrace_ne_zero C p X
  simp [norm_ne_zero_iff.mpr hd]

end MTC.PropertyF.Pivotal
end
