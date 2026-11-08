module
public import MTC.PropertyF.Pivotal.Statement
public import MTC.Center.Induction.PivotalCentrality

/-! # The actual Drinfeld centre is categorically nondegenerate -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory MTC.Fusion
namespace MTC.PropertyF.Pivotal
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "Z" => MTC.PropertyF.Reduction.bundledCenter C

/-- The actual Drinfeld centre has only the tensor unit as transparent simple
object. No pivotal structure or positivity is needed for this step. -/
theorem isNondegenerate_center : IsNondegenerate Z := by
  intro i hi
  letI : Simple (simples Z i) := simples_simple Z i
  have ht : ∀ W : CategoryTheory.Center C.Obj,
      MTC.Center.Centralizes (simples Z i) W := hi
  obtain ⟨e⟩ := MTC.Center.Induction.center_transparent_simple_iso_unit (C := C) ht
  apply simples_injective Z
  exact ⟨e ≪≫ (unitIndex_iso Z).some.symm⟩

end MTC.PropertyF.Pivotal
end
