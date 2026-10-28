module
public import PropertyF.Ground.CentreInduction.ForgetDualUnit
public import PropertyF.Ground.Centre.Product
public import PropertyF.Ground.Dimensions.DoubleDualPairing
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix

open PropertyF.Ground.Dimensions

section
/-! Lift a pivotal structure once its transported components are central. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (Center D)]
local notation "𝒵" => Center D
variable (p : PivotalStructure (C := D))

/-- The sole remaining obstruction to lifting the pivotal structure is the
half-braiding intertwining equation for the transported components. -/
def PivotalComponentsCentral : Prop :=
  ∀ (Z : 𝒵) (T : D),
    (transportedPivotalHom p Z ▷ T) ≫ (((Zᘁ)ᘁ).2.β T).hom =
      (Z.2.β T).hom ≫ (T ◁ transportedPivotalHom p Z)

/-- Central transported components assemble into a pivotal structure on the
actual centre; naturality, tensor and unit coherence are proved. -/
def liftedPivotalStructure (hc : PivotalComponentsCentral p) :
    PivotalStructure (C := 𝒵) where
  iso Z := by
    let u := transportedPivotalHom p Z
    let f : Z ⟶ ((Zᘁ)ᘁ) := ⟨u, hc Z⟩
    letI : IsIso f.f := by change IsIso u; dsimp only [u, transportedPivotalHom]; infer_instance
    exact Center.isoMk f
  naturality f := by
    apply Center.ext
    simpa only [Center.comp_f, Center.isoMk_hom] using
      transported_pivotal_natural p f
  tensor X Y := by
    apply Center.ext
    simpa only [Center.comp_f, Center.tensor_f,
      Center.isoMk_hom, Center.tensor_fst] using
      (transported_pivotal_tensor p X Y).symm
  unit := by
    apply Center.ext
    simp only [Center.isoMk_hom]
    exact transported_pivotal_unit p

/-- The lifted component agrees with the original pivotal component. -/
theorem liftedPivotalStructure_compatible {p : PivotalStructure (C := D)}
    (hc : PivotalComponentsCentral p) (Z : 𝒵) :
    PivotalCompatibleAt p (liftedPivotalStructure p hc) Z := by
  simp [PivotalCompatibleAt, liftedPivotalStructure, transportedPivotalHom, Category.assoc]

end

end PropertyF.Ground.CentreInduction

end
end

/-! Pivotal components on canonical positive centre images. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [RigidCategory (Center D)]
local notation "Z⁺" => Functor.obj (Center.ofBraided D)

/-- The positive centre embedding preserves right duals up to the canonical isomorphism. -/
def positiveDualIso (T : D) : (Z⁺ T)ᘁ ≅ Z⁺ (Tᘁ) :=
  rightDualIso HasRightDual.exact (Centre.positiveExactPairing T (Tᘁ))

/-- Forgetting the positive dual comparison gives the base dual comparison. -/
theorem positiveDualIso_forget (T : D) :
    (positiveDualIso T).hom.f = (forgetDualIso (Z⁺ T)).hom := by
  let F := Center.ofBraided D
  have hc : (@ExactPairing.coevaluation (Center D) _ _
      (Z⁺ T) (Z⁺ (Tᘁ))
      (Centre.positiveExactPairing T (Tᘁ))).f = η_ T (Tᘁ) := by
    change (ε F ≫ F.map (η_ T (Tᘁ)) ≫ δ F T (Tᘁ)).f = _
    simp [F]
  unfold positiveDualIso forgetDualIso rightDualIso rightAdjointMate
  simp only [Center.comp_f, Center.rightUnitor_inv_f,
    Center.leftUnitor_hom_f, Center.whiskerLeft_f,
    Center.whiskerRight_f, Center.associator_inv_f,
    Center.id_f, hc]
  rfl

/-- The comparison between the double duals of an object and its positive lift. -/
def positiveDoubleDualIso (T : D) : ((Z⁺ T)ᘁ)ᘁ ≅ Z⁺ ((Tᘁ)ᘁ) :=
  rightDualIsoMap (positiveDualIso T).symm ≪≫ positiveDualIso (Tᘁ)

/-- Forgetting also preserves the inverse positive dual comparison. -/
theorem positiveDualIso_inv_forget (T : D) :
    (positiveDualIso T).inv.f = (forgetDualIso (Z⁺ T)).inv :=
  (Iso.inv_eq_inv ((Center.forget D).mapIso (positiveDualIso T))
    (forgetDualIso (Z⁺ T))).2 (positiveDualIso_forget T)

/-- Forgetting the positive double-dual comparison gives the base comparison. -/
theorem positiveDoubleDualIso_forget (T : D) :
    (positiveDoubleDualIso T).hom.f = (forgetDoubleDualIso (Z⁺ T)).hom := by
  simpa only [positiveDoubleDualIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap,
    Center.comp_f, forgetDoubleDualIso, positiveDualIso_forget, positiveDualIso_inv_forget] using
    forgetDualIso_natural (positiveDualIso T).inv

/-- Forgetting also preserves the inverse positive double-dual comparison. -/
theorem positiveDoubleDualIso_inv_forget (T : D) :
    (positiveDoubleDualIso T).inv.f = (forgetDoubleDualIso (Z⁺ T)).inv :=
  (Iso.inv_eq_inv ((Center.forget D).mapIso (positiveDoubleDualIso T))
    (forgetDoubleDualIso (Z⁺ T))).2 (positiveDoubleDualIso_forget T)

variable (p : PivotalStructure (C := D))

/-- The pivotal component transported to the positive centre lift. -/
def positivePivotalComponent (T : D) :
    Z⁺ T ≅ ((Z⁺ T)ᘁ)ᘁ :=
  (Center.ofBraided D).mapIso (p.iso T) ≪≫ (positiveDoubleDualIso T).symm

/-- Forgetting a positive pivotal component gives the transported component. -/
theorem positivePivotalComponent_forget (T : D) :
    (positivePivotalComponent p T).hom.f = transportedPivotalHom p (Z⁺ T) :=
  congrArg ((p.iso T).hom ≫ ·) (positiveDoubleDualIso_inv_forget T)

end PropertyF.Ground.CentreInduction

end

/-! Transfer a compatible pivotal structure to positive spherical centre data. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u})
  [RigidCategory (Center C.Obj)]
  [IsFusionCategory (Center C.Obj)]
local notation "𝒵" => Center C.Obj
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- The scalar of a centre unit endomorphism is unchanged by forgetting. -/
theorem center_unitScalar_forget (a : End (𝟙_ (𝒵))) :
    unitScalar 𝒵ᶠ a = unitScalar C (End.of a.asHom.f) :=
  (unit_algebraMap_bijective C).1 <|
    (End.ext (congrArg (fun x : End (𝟙_ (𝒵)) => x.asHom.f)
      (algebraMap_unitScalar 𝒵ᶠ a))).trans (algebraMap_unitScalar C _).symm

/-- Compatible pivotal components have identical scalar dimensions after forgetting. -/
theorem center_pivotalDimension_forget
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := 𝒵)} {Z : 𝒵}
    (hcompat : PivotalCompatibleAt p pZ Z) :
    pivotalDimension 𝒵ᶠ pZ Z = pivotalDimension C p Z.1 :=
  (center_unitScalar_forget C (pZ.rightTrace (𝟙 Z))).trans
    (congrArg (fun f => unitScalar C (End.of f)) (forget_trace_of_pivotal_component hcompat))

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {C : BraidedFusionCategory.{v,u}}
  [RigidCategory (Center C.Obj)]
  [IsFusionCategory (Center C.Obj)]
local notation "𝒵" => Center C.Obj
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- A compatible lift of a positive pivotal structure is spherical and has
FP dimensions on the centre. -/
theorem center_positive_spherical_of_compatible_pivotal
    {p : PivotalStructure (C := C.Obj)} (hsimple : PivotalHasFPDimensions C p)
    {pZ : PivotalStructure (C := 𝒵)} (hcompat : ∀ Z : 𝒵, PivotalCompatibleAt p pZ Z) :
    pZ.IsSpherical ∧ PivotalHasFPDimensions 𝒵ᶠ pZ := by
  let D := 𝒵ᶠ
  have hd (i : Fin (rank D)) : pivotalDimension D pZ (simples D i) =
      (fpSimple D i : ℂ) :=
    (center_pivotalDimension_forget C (hcompat _)).trans <|
      (pivotalDimension_eq_fp hsimple _).trans <| congrArg (fun x : ℝ => (x : ℂ)) <|
        (Integrate.center_forget_fpDimension C _).trans (fpDimension_simple D i)
  refine ⟨(pivotal_spherical_iff_simple_dimensions_real D pZ).2 ?_, hd⟩
  intro i
  simp [hd]

end PropertyF.Ground.CentreInduction
