module
public import PropertyF.Ground.Centre.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! Exactness of the centre forgetful functor. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C]

/-- Forgetting a centre half-braiding preserves each kernel. -/
instance centerForgetPreservesKernel {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) (CategoryTheory.Center.forget C) := by
  apply preservesLimit_of_preserves_limit_cone (centerKernelIsLimit f)
  exact (isLimitMapConeForkEquiv' (CategoryTheory.Center.forget C)
    (centerKernel_condition f)).symm (kernelIsKernel f.f)

/-- Forgetting a centre half-braiding preserves each cokernel. -/
instance centerForgetPreservesCokernel {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (CategoryTheory.Center.forget C) := by
  apply preservesColimit_of_preserves_colimit_cocone (centerCokernelIsColimit f)
  exact (isColimitMapCoconeCoforkEquiv' (CategoryTheory.Center.forget C)
    (centerCokernel_condition f)).symm (cokernelIsCokernel f.f)

/-- The centre forgetful functor preserves all finite limits. -/
instance centerForgetPreservesFiniteLimits :
    PreservesFiniteLimits (CategoryTheory.Center.forget C) :=
  CategoryTheory.Functor.preservesFiniteLimits_of_preservesKernels _

/-- The centre forgetful functor preserves all finite colimits. -/
instance centerForgetPreservesFiniteColimits :
    PreservesFiniteColimits (CategoryTheory.Center.forget C) :=
  CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels _

end PropertyF.Ground.Centre
