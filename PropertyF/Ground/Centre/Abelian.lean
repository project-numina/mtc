module
public import PropertyF.Ground.Centre.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! # Additive and abelian structure on the Drinfeld centre. -/

/-! Binary biproducts in the Drinfeld centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C]

local instance (U : C) : PreservesBinaryBiproducts (tensorRight U) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

local instance (U : C) : PreservesBinaryBiproducts (tensorLeft U) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The distributive half-braiding of a binary direct sum. -/
def sumHalfIso (X Y : CategoryTheory.Center C) (U : C) :
    (X.1 ⊞ Y.1) ⊗ U ≅ U ⊗ (X.1 ⊞ Y.1) :=
  Functor.mapBiprod (tensorRight U) X.1 Y.1 ≪≫
    biprod.mapIso (X.2.β U) (Y.2.β U) ≪≫
      (Functor.mapBiprod (tensorLeft U) X.1 Y.1).symm

private theorem inl_mapBiprod_inv (X Y : CategoryTheory.Center C) (U : C) :
    biprod.inl ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv = biprod.inl ▷ U := by
  rw [Functor.mapBiprod_inv, biprod.inl_desc]
  rfl

private theorem inr_mapBiprod_inv (X Y : CategoryTheory.Center C) (U : C) :
    biprod.inr ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv = biprod.inr ▷ U := by
  rw [Functor.mapBiprod_inv, biprod.inr_desc]
  rfl

@[reassoc]
theorem inl_sumHalfIso (X Y : CategoryTheory.Center C) (U : C) :
    biprod.inl ▷ U ≫ (sumHalfIso X Y U).hom = halfBraidingHom X U ≫ U ◁ biprod.inl := by
  have h : biprod.inl ▷ U ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).hom = biprod.inl := by
    apply (Iso.eq_comp_inv (Functor.mapBiprod (tensorRight U) X.1 Y.1)).mp
    rw [Functor.mapBiprod_inv, biprod.inl_desc]
    rfl
  dsimp only [sumHalfIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [biprod.mapIso, biprod.inl_map]
  rw [Functor.mapBiprod_inv, Category.assoc, biprod.inl_desc]
  rfl

@[reassoc]
theorem inr_sumHalfIso (X Y : CategoryTheory.Center C) (U : C) :
    biprod.inr ▷ U ≫ (sumHalfIso X Y U).hom = halfBraidingHom Y U ≫ U ◁ biprod.inr := by
  have h : biprod.inr ▷ U ≫ (Functor.mapBiprod (tensorRight U) X.1 Y.1).hom = biprod.inr := by
    apply (Iso.eq_comp_inv (Functor.mapBiprod (tensorRight U) X.1 Y.1)).mp
    rw [Functor.mapBiprod_inv, biprod.inr_desc]
    rfl
  dsimp only [sumHalfIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [biprod.mapIso, biprod.inr_map]
  rw [Functor.mapBiprod_inv, Category.assoc, biprod.inr_desc]
  rfl

/-- Naturality of the half-braiding of a direct sum. -/
theorem sumHalfIso_naturality (X Y : CategoryTheory.Center C) {U V : C} (f : U ⟶ V) :
    (X.1 ⊞ Y.1) ◁ f ≫ (sumHalfIso X Y V).hom =
      (sumHalfIso X Y U).hom ≫ f ▷ (X.1 ⊞ Y.1) := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inl_desc]
    simp [← whisker_exchange_assoc, inl_sumHalfIso]
    rw [HalfBraiding.naturality_assoc, ← Category.assoc, whisker_exchange]
    simp only [Category.assoc]
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inr_desc]
    simp [← whisker_exchange_assoc, inr_sumHalfIso]
    rw [HalfBraiding.naturality_assoc, ← Category.assoc, whisker_exchange]
    simp only [Category.assoc]

/-- Compatibility of the sum half-braiding with tensor products. -/
theorem sumHalfIso_monoidal (X Y : CategoryTheory.Center C) (U V : C) :
    (sumHalfIso X Y (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ ((sumHalfIso X Y U).hom ▷ V) ≫ (α_ _ _ _).hom ≫
        (U ◁ (sumHalfIso X Y V).hom) ≫ (α_ _ _ _).inv := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight (U ⊗ V)) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · simp only [← Category.assoc, inl_mapBiprod_inv]
    simp only [Category.assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, inl_sumHalfIso, HalfBraiding.monoidal]
    simp only [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
      ← whiskerLeft_comp_assoc, inl_sumHalfIso]
    simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right]
  · simp only [← Category.assoc, inr_mapBiprod_inv]
    simp only [Category.assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, inr_sumHalfIso, HalfBraiding.monoidal]
    simp only [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
      ← whiskerLeft_comp_assoc, inr_sumHalfIso]
    simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right]

/-- The centre object whose underlying object is a binary biproduct. -/
def centerBiprod (X Y : CategoryTheory.Center C) : CategoryTheory.Center C :=
  ⟨X.1 ⊞ Y.1,
    { β := sumHalfIso X Y
      monoidal := sumHalfIso_monoidal X Y
      naturality := fun f => sumHalfIso_naturality X Y f }⟩

/-- The usual inclusion is a centre morphism. -/
def centerBiprodInl (X Y : CategoryTheory.Center C) : X ⟶ centerBiprod X Y :=
  ⟨biprod.inl, fun U => inl_sumHalfIso X Y U⟩

/-- The other usual inclusion is a centre morphism. -/
def centerBiprodInr (X Y : CategoryTheory.Center C) : Y ⟶ centerBiprod X Y :=
  ⟨biprod.inr, fun U => inr_sumHalfIso X Y U⟩

/-- The first projection commutes with the sum half-braiding. -/
theorem sumHalfIso_fst (X Y : CategoryTheory.Center C) (U : C) :
    biprod.fst ▷ U ≫ halfBraidingHom X U = (sumHalfIso X Y U).hom ≫ U ◁ biprod.fst := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inl_desc]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inl_sumHalfIso]
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inr_desc]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inr_sumHalfIso]

/-- The second projection commutes with the sum half-braiding. -/
theorem sumHalfIso_snd (X Y : CategoryTheory.Center C) (U : C) :
    biprod.snd ▷ U ≫ halfBraidingHom Y U = (sumHalfIso X Y U).hom ≫ U ◁ biprod.snd := by
  apply (cancel_epi (Functor.mapBiprod (tensorRight U) X.1 Y.1).inv).mp
  apply biprod.hom_ext'
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inl_desc]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inl_sumHalfIso]
  · simp only [← Category.assoc, Functor.mapBiprod_inv, biprod.inr_desc]
    simp [← comp_whiskerRight, ← whiskerLeft_comp, inr_sumHalfIso]


/-- The biproduct projections lift to centre morphisms. -/
def centerBiprodFst (X Y : CategoryTheory.Center C) : centerBiprod X Y ⟶ X :=
  ⟨biprod.fst, fun U => sumHalfIso_fst X Y U⟩

/-- The second biproduct projection as a centre morphism. -/
def centerBiprodSnd (X Y : CategoryTheory.Center C) : centerBiprod X Y ⟶ Y :=
  ⟨biprod.snd, fun U => sumHalfIso_snd X Y U⟩

/-- The underlying binary biproduct yields a bicone in the centre. -/
def centerBinaryBicone (X Y : CategoryTheory.Center C) : BinaryBicone X Y where
  pt := centerBiprod X Y
  fst := centerBiprodFst X Y
  snd := centerBiprodSnd X Y
  inl := centerBiprodInl X Y
  inr := centerBiprodInr X Y
  inl_fst := by
    apply CategoryTheory.Center.ext
    change biprod.inl ≫ biprod.fst = 𝟙 X.1
    exact biprod.inl_fst
  inl_snd := by
    apply CategoryTheory.Center.ext
    change biprod.inl ≫ biprod.snd = 0
    exact biprod.inl_snd
  inr_fst := by
    apply CategoryTheory.Center.ext
    change biprod.inr ≫ biprod.fst = 0
    exact biprod.inr_fst
  inr_snd := by
    apply CategoryTheory.Center.ext
    change biprod.inr ≫ biprod.snd = 𝟙 Y.1
    exact biprod.inr_snd

/-- The lifted bicone is a bilimit. -/
def centerBinaryBilimit (X Y : CategoryTheory.Center C) : (centerBinaryBicone X Y).IsBilimit :=
  isBinaryBilimitOfTotal _ (by
    apply CategoryTheory.Center.ext
    exact biprod.total)

instance centerHasBinaryBiproducts : HasBinaryBiproducts (CategoryTheory.Center C) where
  has_binary_biproduct X Y := ⟨⟨centerBinaryBicone X Y, centerBinaryBilimit X Y⟩⟩

/-- Zero and binary biproducts provide all finite biproducts in the centre. -/
instance centerHasFiniteBiproducts [HasZeroObject C] :
    HasFiniteBiproducts (CategoryTheory.Center C) := by
  let _ : HasFiniteProducts (CategoryTheory.Center C) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

end PropertyF.Ground.Centre

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
theorem kernelHalfIso_ι {X Y : CategoryTheory.Center C} (f : X ⟶ Y) {U : C} :
    (kernelHalfIso f U).hom ≫ U ◁ kernel.ι f.f =
      (kernel.ι f.f ▷ U) ≫ (X.2.β U).hom := by
  simp only [kernelHalfIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (PreservesKernel.iso (tensorRight U) f.f).hom ≫
    (kernel.mapIso (f.f ▷ U) (U ◁ f.f) (X.2.β U) (Y.2.β U) (f.comm U)).hom ≫
    ((PreservesKernel.iso (tensorLeft U) f.f).inv ≫ (tensorLeft U).map (kernel.ι f.f)) = _
  rw [PreservesKernel.iso_inv_ι, kernel.mapIso_hom, PreservesKernel.iso_hom]
  change kernelComparison f.f (tensorRight U) ≫
      (kernel.lift (U ◁ f.f) (kernel.ι (f.f ▷ U) ≫ (X.2.β U).hom) _ ≫
        kernel.ι (U ◁ f.f)) = _
  rw [kernel.lift_ι, ← Category.assoc]
  exact congrArg (fun g ↦ g ≫ (X.2.β U).hom)
    (kernelComparison_comp_ι f.f (tensorRight U))

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
    congrArg (fun k => k ≫ g ▷ X.1) (kernelHalfIso_ι (U := U) f).symm

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
  ⟨kernel.ι f.f, fun U => (kernelHalfIso_ι (U := U) f).symm⟩

/-- The kernel inclusion followed by the original map is zero. -/
theorem centerKernel_condition {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    centerKernelι f ≫ f = 0 :=
  CategoryTheory.Center.ext _ _ (kernel.condition f.f)

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
theorem centerSimple_of_underlying {Z : CategoryTheory.Center C} [Simple Z.1] : Simple Z :=
  have : Simple ((CategoryTheory.Center.forget C).obj Z) := ‹Simple Z.1›
  (CategoryTheory.Center.forget C).simple_of_simple_obj Z

/-- A simple underlying tensor unit remains simple in the centre. -/
theorem centerUnitSimple [Simple (𝟙_ C)] : Simple (𝟙_ (CategoryTheory.Center C)) :=
  have : Simple (𝟙_ (CategoryTheory.Center C)).1 := ‹Simple (𝟙_ C)›
  centerSimple_of_underlying

end PropertyF.Ground.Centre

/-! Cokernels of centre morphisms in a rigid abelian category. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C]

local instance (U : C) : (tensorLeft U).IsLeftAdjoint :=
  ⟨⟨tensorLeft (ᘁU), ⟨tensorLeftAdjunction (ᘁU) U⟩⟩⟩

local instance (U : C) : (tensorRight U).IsLeftAdjoint :=
  ⟨⟨tensorRight (Uᘁ), ⟨tensorRightAdjunction U (Uᘁ)⟩⟩⟩

/-- The half-braiding induced on the cokernel by tensoring's colimit preservation. -/
def cokernelHalfIso {X Y : CategoryTheory.Center C} (f : X ⟶ Y) (U : C) :
    cokernel f.f ⊗ U ≅ U ⊗ cokernel f.f :=
  PreservesCokernel.iso (tensorRight U) f.f ≪≫
    cokernel.mapIso (f.f ▷ U) (U ◁ f.f) (X.2.β U) (Y.2.β U) (f.comm U) ≪≫
      (PreservesCokernel.iso (tensorLeft U) f.f).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cokernel projection intertwines the induced half-braiding. -/
@[reassoc]
theorem cokernelHalfIso_π {X Y : CategoryTheory.Center C} (f : X ⟶ Y) {U : C} :
    cokernel.π f.f ▷ U ≫ (cokernelHalfIso f U).hom =
      (Y.2.β U).hom ≫ U ◁ cokernel.π f.f := by
  simp only [cokernelHalfIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  change (((tensorRight U).map (cokernel.π f.f) ≫ (PreservesCokernel.iso (tensorRight U) f.f).hom) ≫
      (cokernel.mapIso (f.f ▷ U) (U ◁ f.f) (X.2.β U) (Y.2.β U) (f.comm U)).hom) ≫
      (PreservesCokernel.iso (tensorLeft U) f.f).inv = _
  rw [PreservesCokernel.π_iso_hom, cokernel.mapIso_hom, PreservesCokernel.iso_inv]
  change (cokernel.π (f.f ▷ U) ≫ cokernel.desc (f.f ▷ U)
    ((Y.2.β U).hom ≫ cokernel.π (U ◁ f.f)) _) ≫
      cokernelComparison f.f (tensorLeft U) = _
  rw [cokernel.π_desc, Category.assoc]
  exact congrArg (fun g ↦ (Y.2.β U).hom ≫ g)
    (π_comp_cokernelComparison f.f (tensorLeft U))

/-- Naturality of the induced cokernel half-braiding. -/
theorem cokernelHalfIso_naturality {X Y : CategoryTheory.Center C} (f : X ⟶ Y)
    {U V : C} (g : U ⟶ V) :
    cokernel f.f ◁ g ≫ (cokernelHalfIso f V).hom =
      (cokernelHalfIso f U).hom ≫ g ▷ cokernel f.f := by
  have : Epi (cokernel.π f.f ▷ U) := by
    change Epi ((tensorRight U).map (cokernel.π f.f))
    infer_instance
  apply (cancel_epi (cokernel.π f.f ▷ U)).mp
  simp only [← Category.assoc, cokernelHalfIso_π]
  rw [← whisker_exchange, Category.assoc, cokernelHalfIso_π]
  rw [HalfBraiding.naturality_assoc, Category.assoc, whisker_exchange]

/-- Tensor compatibility of the induced cokernel half-braiding. -/
theorem cokernelHalfIso_monoidal {X Y : CategoryTheory.Center C} (f : X ⟶ Y) (U V : C) :
    (cokernelHalfIso f (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ ((cokernelHalfIso f U).hom ▷ V) ≫ (α_ _ _ _).hom ≫
        (U ◁ (cokernelHalfIso f V).hom) ≫ (α_ _ _ _).inv := by
  have : Epi (cokernel.π f.f ▷ (U ⊗ V)) := by
    change Epi ((tensorRight (U ⊗ V)).map (cokernel.π f.f))
    infer_instance
  apply (cancel_epi (cokernel.π f.f ▷ (U ⊗ V))).mp
  simp only [← Category.assoc, cokernelHalfIso_π, HalfBraiding.monoidal]
  simp only [Category.assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    cokernelHalfIso_π]
  simp only [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, cokernelHalfIso_π]
  simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right]

/-- The underlying cokernel acquires a natural half-braiding. -/
def centerCokernel {X Y : CategoryTheory.Center C} (f : X ⟶ Y) : CategoryTheory.Center C :=
  ⟨cokernel f.f,
    { β := cokernelHalfIso f
      monoidal := cokernelHalfIso_monoidal f
      naturality := fun g => cokernelHalfIso_naturality f g }⟩

/-- Cokernel projection as a morphism in the centre. -/
def centerCokernelπ {X Y : CategoryTheory.Center C} (f : X ⟶ Y) : Y ⟶ centerCokernel f :=
  ⟨cokernel.π f.f, fun U => cokernelHalfIso_π (U := U) f⟩

/-- The original map followed by the cokernel projection is zero. -/
theorem centerCokernel_condition {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    f ≫ centerCokernelπ f = 0 :=
  CategoryTheory.Center.ext _ _ (cokernel.condition f.f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Universal descent from the centre cokernel. -/
def centerCokernelDesc {X Y Z : CategoryTheory.Center C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : f ≫ g = 0) : centerCokernel f ⟶ Z := by
  have h' : f.f ≫ g.f = 0 := congrArg CategoryTheory.Center.Hom.f h
  let k := cokernel.desc f.f g.f h'
  refine ⟨k, ?_⟩
  intro U
  have : Epi (cokernel.π f.f ▷ U) := by
    change Epi ((tensorRight U).map (cokernel.π f.f))
    infer_instance
  apply (cancel_epi (cokernel.π f.f ▷ U)).mp
  simp only [← Category.assoc, ← comp_whiskerRight]
  have hk : cokernel.π f.f ≫ k = g.f := cokernel.π_desc _ _ _
  rw [hk]
  change (g.f ▷ U) ≫ (Z.2.β U).hom =
    (cokernel.π f.f ▷ U ≫ (cokernelHalfIso f U).hom) ≫ U ◁ k
  rw [cokernelHalfIso_π, Category.assoc, ← whiskerLeft_comp, hk]
  exact g.comm U

/-- The lifted cokernel satisfies the universal property in the centre. -/
def centerCokernelIsColimit {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (centerCokernelπ f) (centerCokernel_condition f)) := by
  apply CokernelCofork.IsColimit.ofπ _ _ (fun g h => centerCokernelDesc f g h)
  · intro W g h
    apply CategoryTheory.Center.ext
    change cokernel.π f.f ≫ cokernel.desc f.f g.f _ = g.f
    exact cokernel.π_desc _ _ _
  · intro W g h m hm
    have h' : f.f ≫ g.f = 0 := congrArg CategoryTheory.Center.Hom.f h
    apply CategoryTheory.Center.ext
    apply (cancel_epi (cokernel.π f.f)).mp
    change cokernel.π f.f ≫ m.f = cokernel.π f.f ≫ cokernel.desc f.f g.f h'
    rw [cokernel.π_desc]
    exact congrArg CategoryTheory.Center.Hom.f hm

/-- The centre has cokernels whenever the underlying category is rigid and abelian. -/
instance centerHasCokernels : HasCokernels (CategoryTheory.Center C) where
  has_colimit f := ⟨⟨CokernelCofork.ofπ (centerCokernelπ f) (centerCokernel_condition f),
    centerCokernelIsColimit f⟩⟩

/-- The forgetful functor sends centre epimorphisms to epimorphisms. -/
instance centerForgetPreservesEpimorphisms : (CategoryTheory.Center.forget C).PreservesEpimorphisms where
  preserves := by
    intro X Y f _
    apply Preadditive.epi_of_cokernel_zero
    have hzero : centerCokernelπ f = 0 := by
      apply (cancel_epi f).mp
      simpa using centerCokernel_condition f
    exact congrArg CategoryTheory.Center.Hom.f hzero

end PropertyF.Ground.Centre

/-! The Drinfeld centre of a rigid abelian monoidal category is abelian. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C]

/-- A monomorphism in the centre is the kernel of its cokernel. -/
@[instance_reducible]
def centerNormalMono {X Y : CategoryTheory.Center C} (f : X ⟶ Y) [Mono f] : NormalMono f := by
  let k := centerKernelLift (centerCokernelπ f) f (centerCokernel_condition f)
  have hk : k ≫ centerKernelι (centerCokernelπ f) = f := by
    apply CategoryTheory.Center.ext
    change kernel.lift (cokernel.π f.f) f.f _ ≫ kernel.ι (cokernel.π f.f) = f.f
    exact kernel.lift_ι _ _ _
  have : Mono f.f := by
    change Mono ((CategoryTheory.Center.forget C).map f)
    infer_instance
  have : IsIso k.f := by
    change IsIso (Abelian.factorThruImage f.f)
    infer_instance
  have : IsIso k := CategoryTheory.Center.isIso_of_f_isIso k
  refine { Z := centerCokernel f
           g := centerCokernelπ f
           w := centerCokernel_condition f
           isLimit := ?_ }
  apply KernelFork.IsLimit.ofι' _ _
  intro W g hg
  let l := centerKernelLift (centerCokernelπ f) g hg
  have hl : l ≫ centerKernelι (centerCokernelπ f) = g := by
    apply CategoryTheory.Center.ext
    change kernel.lift (cokernel.π f.f) g.f _ ≫ kernel.ι (cokernel.π f.f) = g.f
    exact kernel.lift_ι _ _ _
  refine ⟨l ≫ inv k, ?_⟩
  calc
    (l ≫ inv k) ≫ f = (l ≫ inv k) ≫ (k ≫ centerKernelι (centerCokernelπ f)) :=
      congrArg (fun t => (l ≫ inv k) ≫ t) hk.symm
    _ = g := by simp [Category.assoc, hl]

/-- An epimorphism in the centre is the cokernel of its kernel. -/
@[instance_reducible]
def centerNormalEpi {X Y : CategoryTheory.Center C} (f : X ⟶ Y) [Epi f] : NormalEpi f := by
  let k := centerCokernelDesc (centerKernelι f) f (centerKernel_condition f)
  have hk : centerCokernelπ (centerKernelι f) ≫ k = f := by
    apply CategoryTheory.Center.ext
    change cokernel.π (kernel.ι f.f) ≫ cokernel.desc (kernel.ι f.f) f.f _ = f.f
    exact cokernel.π_desc _ _ _
  have : Epi f.f := by
    change Epi ((CategoryTheory.Center.forget C).map f)
    infer_instance
  have : IsIso k.f := by
    change IsIso (Abelian.factorThruCoimage f.f)
    infer_instance
  have : IsIso k := CategoryTheory.Center.isIso_of_f_isIso k
  refine { W := centerKernel f
           g := centerKernelι f
           w := centerKernel_condition f
           isColimit := ?_ }
  apply CokernelCofork.IsColimit.ofπ' _ _
  intro W g hg
  let l := centerCokernelDesc (centerKernelι f) g hg
  have hl : centerCokernelπ (centerKernelι f) ≫ l = g := by
    apply CategoryTheory.Center.ext
    change cokernel.π (kernel.ι f.f) ≫ cokernel.desc (kernel.ι f.f) g.f _ = g.f
    exact cokernel.π_desc _ _ _
  refine ⟨inv k ≫ l, ?_⟩
  calc
    f ≫ (inv k ≫ l) = (centerCokernelπ (centerKernelι f) ≫ k) ≫ (inv k ≫ l) :=
      congrArg (fun t => t ≫ (inv k ≫ l)) hk.symm
    _ = g := by simp [Category.assoc, hl]

/-- The centre of a rigid abelian monoidal category is abelian. -/
instance centerAbelian : Abelian (CategoryTheory.Center C) where
  normalMonoOfMono f := ⟨centerNormalMono f⟩
  normalEpiOfEpi f := ⟨centerNormalEpi f⟩

end PropertyF.Ground.Centre
