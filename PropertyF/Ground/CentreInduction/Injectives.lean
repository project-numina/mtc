module
public import PropertyF.Ground.CentreInduction.FiniteSimples
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
open CategoryTheory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

/-- Induction sends every base object to an injective centre object. -/
theorem induction_injective (X : C.Obj) : Injective ((induction C).obj X) := by
  letI : (induction C).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (actualAdjunction C)
  letI : Injective X := object_injective C X
  infer_instance



end PropertyF.Ground.CentreInduction
