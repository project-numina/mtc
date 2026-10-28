module
public import PropertyF.Ground.Integrate.ScalarTwistTransport
public import PropertyF.Ground.Fusion.FunctorDimension
public import PropertyF.Ground.Modular.SMatrix

/-! FP dimensions, pivotal traces, and categorical S matrices under scalar twist. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.ScalarTwist
universe v u
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- FP dimension is unchanged on every object. -/
theorem fpDimension_twist (X : C.Obj) :
    fpDimension (category C σ) X = fpDimension C X := by
  let E := conjugate C σ
  let F := E.equivalence.functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  letI : F.Faithful := inferInstanceAs E.equivalence.functor.Faithful
  letI : F.Monoidal := E.monoidal
  exact fpDimension_functor C (category C σ) F X

/-- A pivotal trace scalar is carried through σ. -/
theorem rightTrace_twist (p : Dimensions.PivotalStructure (C := C.Obj))
    {X : C.Obj} (f : X ⟶ X) :
    Dimensions.groundUnitScalarEquiv (category C σ) ((pivotal C σ p).rightTrace f) =
      σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace f)) := by
  simp only [Dimensions.groundUnitScalarEquiv_apply]
  exact unitScalar_twist C σ _


end PropertyF.Ground.ScalarTwist
