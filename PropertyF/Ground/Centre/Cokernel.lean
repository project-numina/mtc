module
public import PropertyF.Ground.Centre.Kernel

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
theorem cokernelHalfIso_π {X Y : CategoryTheory.Center C} (f : X ⟶ Y) (U : C) :
    cokernel.π f.f ▷ U ≫ (cokernelHalfIso f U).hom =
      (Y.2.β U).hom ≫ U ◁ cokernel.π f.f := by
  simp only [cokernelHalfIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc]
  change (((tensorRight U).map (cokernel.π f.f) ≫ (PreservesCokernel.iso (tensorRight U) f.f).hom) ≫
      (cokernel.mapIso (f.f ▷ U) (U ◁ f.f) (X.2.β U) (Y.2.β U) (f.comm U)).hom) ≫
      (PreservesCokernel.iso (tensorLeft U) f.f).inv = _
  rw [PreservesCokernel.π_iso_hom, cokernel.mapIso_hom]
  simp only [cokernel.map, PreservesCokernel.iso_inv]
  change (cokernel.π (f.f ▷ U) ≫ cokernel.desc (f.f ▷ U)
    ((Y.2.β U).hom ≫ cokernel.π (U ◁ f.f)) _) ≫
      cokernelComparison f.f (tensorLeft U) = _
  rw [cokernel.π_desc, Category.assoc]
  change (Y.2.β U).hom ≫ (cokernel.π ((tensorLeft U).map f.f) ≫
    cokernelComparison f.f (tensorLeft U)) = _
  rw [π_comp_cokernelComparison]
  rfl

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
  ⟨cokernel.π f.f, fun U => cokernelHalfIso_π f U⟩

/-- The original map followed by the cokernel projection is zero. -/
theorem centerCokernel_condition {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    f ≫ centerCokernelπ f = 0 := by
  apply CategoryTheory.Center.ext
  change f.f ≫ cokernel.π f.f = 0
  exact cokernel.condition f.f

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
