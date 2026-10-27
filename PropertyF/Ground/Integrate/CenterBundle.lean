module
public import PropertyF.Ground.Integrate.FunctorUniverse
public import PropertyF.Ground.Centre.Abelian

/-! Bundle the actual centre conditionally on its remaining fusion proofs. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Integrate
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- The actual centre, provided its unproved rigidity and finite
semisimplicity obligations are supplied as explicit instances. -/
def bundledCenter : BraidedFusionCategory.{v,max u v} where
  Obj := CategoryTheory.Center C.Obj

/-- The actual centre forgetful functor preserves FP dimension once the
centre is proved to be a rigid fusion category. -/
theorem center_forget_fpDimension (X : (bundledCenter C).Obj) :
    fpDimension C ((CategoryTheory.Center.forget C.Obj).obj X) = fpDimension (bundledCenter C) X := by
  let ha : (CategoryTheory.Center.forget C.Obj).Additive := Centre.centerForgetAdditive
  let hf : (CategoryTheory.Center.forget C.Obj).Faithful := Centre.centerForgetFaithful
  let hm : (CategoryTheory.Center.forget C.Obj).Monoidal := inferInstance
  exact @fpDimension_functor_universe (bundledCenter C) C (CategoryTheory.Center.forget C.Obj)
    ha hf hm X

end PropertyF.Ground.Integrate
