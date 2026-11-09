module
public import MTC.PropertyF.Pivotal.MainTheorems
public import MTC.PropertyF.Pivotal.ObjectwiseConsequences

/-! # Objectwise corollary reduced to the closure lemma -/

@[expose] public noncomputable section
open CategoryTheory MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
set_option backward.isDefEq.respectTransparency false
universe v u
variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
local notation "G" => bundledGenerated C X

/-- A generated nondegenerate pivotal category with nonintegral squared FP
dimension of its generator cannot have property F. -/
theorem generated_not_propertyF_of_nonintegral_sq_of_nondegenerate
    (hp : Nonempty (PivotalStructure (C := (bundledGenerated C X).Obj)))
    (hn : IsNondegenerate G)
    (hX : ¬ WeaklyIntegral (fpDimension C X ^ 2)) : ¬ HasPropertyF (bundledGenerated C X).Obj := by
  intro hF
  have hw := (nondegenerateMainStatement_proved G hp hn hF).2.2
  exact hX (generated_simple_fpDimension_sq_integral C X hw)

/-- The entire objectwise manuscript corollary follows from the closure
lemma, with no further mathematical assumptions. -/
theorem objectwiseStatement_of_closure (hclosure : ClosureStatement.{v,u}) :
    ObjectwiseStatement.{v,u} := by
  intro D Y _ hcase hY
  apply eventually_infinite_braidImages_of_not_objectPropertyF D Y
  apply not_objectPropertyF_of_generated_not_propertyF D Y hclosure
  rcases hcase with ⟨hp, hn⟩ | hc
  · exact generated_not_propertyF_of_nonintegral_sq_of_nondegenerate D Y hp hn hY
  · exact generated_not_propertyF_of_nonintegral_sq_of_conjugate D Y hc hY

end MTC.PropertyF.Pivotal
end
