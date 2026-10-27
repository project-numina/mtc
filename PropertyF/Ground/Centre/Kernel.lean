module
public import PropertyF.Ground.Centre.Biproduct
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! Kernels of centre morphisms in a rigid abelian category. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C]

local instance (U : C) : (tensorLeft U).IsRightAdjoint :=
  ⟨⟨tensorLeft (Uᘁ), ⟨tensorLeftAdjunction U (Uᘁ)⟩⟩⟩

local instance (U : C) : (tensorRight U).IsRightAdjoint :=
  ⟨⟨tensorRight (ᘁU), ⟨tensorRightAdjunction (ᘁU) U⟩⟩⟩

/-- The half-braiding induced on the kernel by preservation of kernels under tensoring. -/
def kernelHalfIso {X Y : CategoryTheory.Center C} (f : X ⟶ Y) (U : C) :
    kernel f.f ⊗ U ≅ U ⊗ kernel f.f :=
  PreservesKernel.iso (tensorRight U) f.f ≪≫
    kernel.mapIso (f.f ▷ U) (U ◁ f.f) (X.2.β U) (Y.2.β U) (f.comm U) ≪≫
      (PreservesKernel.iso (tensorLeft U) f.f).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The kernel inclusion intertwines the induced half-braiding. -/
@[reassoc]
theorem kernelHalfIso_ι {X Y : CategoryTheory.Center C} (f : X ⟶ Y) (U : C) :
    (kernelHalfIso f U).hom ≫ U ◁ kernel.ι f.f =
      (kernel.ι f.f ▷ U) ≫ (X.2.β U).hom := by
  simp only [kernelHalfIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (PreservesKernel.iso (tensorRight U) f.f).hom ≫
      (kernel.mapIso (f.f ▷ U) (U ◁ f.f) (X.2.β U) (Y.2.β U) (f.comm U)).hom ≫
      ((PreservesKernel.iso (tensorLeft U) f.f).inv ≫ (tensorLeft U).map (kernel.ι f.f)) = _
  rw [PreservesKernel.iso_inv_ι (tensorLeft U) f.f]
  rw [kernel.mapIso_hom]
  simp only [kernel.map, PreservesKernel.iso_hom]
  change kernelComparison f.f (tensorRight U) ≫
      (kernel.lift (U ◁ f.f) (kernel.ι (f.f ▷ U) ≫ (X.2.β U).hom) _ ≫
        kernel.ι (U ◁ f.f)) = _
  rw [kernel.lift_ι, ← Category.assoc]
  change (kernelComparison f.f (tensorRight U) ≫ kernel.ι ((tensorRight U).map f.f)) ≫
      (X.2.β U).hom = _
  rw [kernelComparison_comp_ι]
  rfl

/-- Naturality of the induced kernel half-braiding. -/
theorem kernelHalfIso_naturality {X Y : CategoryTheory.Center C} (f : X ⟶ Y)
    {U V : C} (g : U ⟶ V) :
    kernel f.f ◁ g ≫ (kernelHalfIso f V).hom = (kernelHalfIso f U).hom ≫ g ▷ kernel f.f := by
  have : Mono (V ◁ kernel.ι f.f) := by
    change Mono ((tensorLeft V).map (kernel.ι f.f))
    infer_instance
  apply (cancel_mono (V ◁ kernel.ι f.f)).mp
  simp only [Category.assoc]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc, kernelHalfIso_ι]
  rw [← Category.assoc, whisker_exchange, Category.assoc, HalfBraiding.naturality]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ g ▷ X.1) (kernelHalfIso_ι f U).symm

/-- Tensor compatibility of the induced kernel half-braiding. -/
theorem kernelHalfIso_monoidal {X Y : CategoryTheory.Center C} (f : X ⟶ Y) (U V : C) :
    (kernelHalfIso f (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ ((kernelHalfIso f U).hom ▷ V) ≫ (α_ _ _ _).hom ≫
        (U ◁ (kernelHalfIso f V).hom) ≫ (α_ _ _ _).inv := by
  have : Mono ((U ⊗ V) ◁ kernel.ι f.f) := by
    change Mono ((tensorLeft (U ⊗ V)).map (kernel.ι f.f))
    infer_instance
  apply (cancel_mono ((U ⊗ V) ◁ kernel.ι f.f)).mp
  simp only [Category.assoc, kernelHalfIso_ι, HalfBraiding.monoidal]
  simp only [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    ← kernelHalfIso_ι]
  simp only [comp_whiskerRight, Category.assoc]
  simp only [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, ← kernelHalfIso_ι]
  simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right]

/-- The underlying kernel acquires a natural half-braiding. -/
def centerKernel {X Y : CategoryTheory.Center C} (f : X ⟶ Y) : CategoryTheory.Center C :=
  ⟨kernel f.f,
    { β := kernelHalfIso f
      monoidal := kernelHalfIso_monoidal f
      naturality := fun g => kernelHalfIso_naturality f g }⟩

/-- Kernel inclusion as a morphism in the centre. -/
def centerKernelι {X Y : CategoryTheory.Center C} (f : X ⟶ Y) : centerKernel f ⟶ X :=
  ⟨kernel.ι f.f, fun U => (kernelHalfIso_ι f U).symm⟩

/-- The kernel inclusion followed by the original map is zero. -/
theorem centerKernel_condition {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    centerKernelι f ≫ f = 0 := by
  apply CategoryTheory.Center.ext
  change kernel.ι f.f ≫ f.f = 0
  exact kernel.condition f.f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Universal lifting into the centre kernel. -/
def centerKernelLift {X Y Z : CategoryTheory.Center C} (f : X ⟶ Y) (g : Z ⟶ X)
    (h : g ≫ f = 0) : Z ⟶ centerKernel f := by
  have h' : g.f ≫ f.f = 0 := by
    have t := congrArg CategoryTheory.Center.Hom.f h
    exact t
  let k := kernel.lift f.f g.f h'
  refine ⟨k, ?_⟩
  intro U
  have : Mono (U ◁ kernel.ι f.f) := by
    change Mono ((tensorLeft U).map (kernel.ι f.f))
    infer_instance
  apply (cancel_mono (U ◁ kernel.ι f.f)).mp
  simp only [Category.assoc, ← whiskerLeft_comp]
  change (k ▷ U) ≫ ((kernelHalfIso f U).hom ≫ U ◁ kernel.ι f.f) =
    (Z.2.β U).hom ≫ (U ◁ (k ≫ kernel.ι f.f))
  rw [kernelHalfIso_ι, kernel.lift_ι]
  rw [← comp_whiskerRight_assoc, kernel.lift_ι]
  exact g.comm U

/-- The lifted kernel satisfies the universal property in the centre. -/
def centerKernelIsLimit {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (centerKernelι f) (centerKernel_condition f)) := by
  apply KernelFork.IsLimit.ofι _ _ (fun g h => centerKernelLift f g h)
  · intro W g h
    apply CategoryTheory.Center.ext
    change kernel.lift f.f g.f _ ≫ kernel.ι f.f = g.f
    exact kernel.lift_ι _ _ _
  · intro W g h m hm
    have h' : g.f ≫ f.f = 0 := congrArg CategoryTheory.Center.Hom.f h
    apply CategoryTheory.Center.ext
    apply (cancel_mono (kernel.ι f.f)).mp
    change m.f ≫ kernel.ι f.f = kernel.lift f.f g.f h' ≫ kernel.ι f.f
    rw [kernel.lift_ι]
    exact congrArg CategoryTheory.Center.Hom.f hm

/-- The centre has kernels whenever the underlying category is rigid and abelian. -/
instance centerHasKernels : HasKernels (CategoryTheory.Center C) where
  has_limit f := ⟨⟨KernelFork.ofι (centerKernelι f) (centerKernel_condition f),
    centerKernelIsLimit f⟩⟩

/-- The forgetful functor sends monomorphisms in the centre to monomorphisms. -/
instance centerForgetPreservesMonomorphisms : (CategoryTheory.Center.forget C).PreservesMonomorphisms where
  preserves := by
    intro X Y f _
    apply Preadditive.mono_of_kernel_zero
    have hzero : centerKernelι f = 0 := by
      apply (cancel_mono f).mp
      simpa using centerKernel_condition f
    exact congrArg CategoryTheory.Center.Hom.f hzero

/-- An object whose underlying object is simple is simple in the centre. -/
theorem centerSimple_of_underlying (Z : CategoryTheory.Center C) [Simple Z.1] : Simple Z := by
  have : Simple ((CategoryTheory.Center.forget C).obj Z) := by
    change Simple Z.1
    infer_instance
  exact (CategoryTheory.Center.forget C).simple_of_simple_obj Z

/-- A simple underlying tensor unit remains simple in the centre. -/
theorem centerUnitSimple [Simple (𝟙_ C)] : Simple (𝟙_ (CategoryTheory.Center C)) := by
  have : Simple (𝟙_ (CategoryTheory.Center C)).1 := by
    change Simple (𝟙_ C)
    infer_instance
  exact centerSimple_of_underlying _

end PropertyF.Ground.Centre
