module
public import PropertyF.Ground.CentreInduction.ForgetDualUnit
public import PropertyF.Ground.Centre.Product
public import PropertyF.Ground.Dimensions.DoubleDualPairing
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix

section
/-! Lift a pivotal structure once its transported components are central. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (CategoryTheory.Center D)]
local notation "𝒵" => CategoryTheory.Center D

/-- The sole remaining obstruction to lifting the pivotal structure is the
half-braiding intertwining equation for the transported components. -/
def PivotalComponentsCentral (p : Dimensions.PivotalStructure (C := D)) : Prop :=
  ∀ (Z : 𝒵) (T : D),
    let u := (p.iso Z.1).hom ≫ (forgetDoubleDualIso Z).inv
    (u ▷ T) ≫ (((Zᘁ)ᘁ).2.β T).hom = (Z.2.β T).hom ≫ (T ◁ u)

/-- Central transported components assemble into a pivotal structure on the
actual centre; naturality, tensor and unit coherence are proved. -/
def liftedPivotalStructure (p : Dimensions.PivotalStructure (C := D))
    (hc : PivotalComponentsCentral p) :
    Dimensions.PivotalStructure (C := 𝒵) where
  iso Z := by
    let u := (p.iso Z.1).hom ≫ (forgetDoubleDualIso Z).inv
    let f : Z ⟶ ((Zᘁ)ᘁ) := ⟨u, hc Z⟩
    letI : IsIso f.f := by change IsIso u; dsimp only [u]; infer_instance
    exact CategoryTheory.Center.isoMk f
  naturality f := by
    apply CategoryTheory.Center.ext
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.isoMk_hom, Category.assoc] using
      transported_pivotal_natural p f
  tensor X Y := by
    apply CategoryTheory.Center.ext
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.tensor_f,
      CategoryTheory.Center.isoMk_hom, CategoryTheory.Center.tensor_fst] using
      (transported_pivotal_tensor p X Y).symm
  unit := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.isoMk_hom]
    convert transported_pivotal_unit p using 1
    all_goals rfl

/-- The lifted component agrees with the original pivotal component. -/
theorem liftedPivotalStructure_compatible {p : Dimensions.PivotalStructure (C := D)}
    (hc : PivotalComponentsCentral p) (Z : 𝒵) :
    PivotalCompatibleAt p (liftedPivotalStructure p hc) Z := by
  simp [PivotalCompatibleAt, liftedPivotalStructure, Category.assoc]

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
  [RightRigidCategory D] [RigidCategory (CategoryTheory.Center D)]

/-- The positive centre embedding preserves right duals up to the canonical isomorphism. -/
def positiveDualIso (T : D) :
    ((CategoryTheory.Center.ofBraided D).obj T)ᘁ ≅
      (CategoryTheory.Center.ofBraided D).obj (Tᘁ) :=
  rightDualIso HasRightDual.exact (Centre.positiveExactPairing T (Tᘁ))

theorem positiveDualIso_forget (T : D) :
    (positiveDualIso T).hom.f =
      (forgetDualIso ((CategoryTheory.Center.ofBraided D).obj T)).hom := by
  let F := CategoryTheory.Center.ofBraided D
  have hc : (@ExactPairing.coevaluation (CategoryTheory.Center D) _ _
      ((CategoryTheory.Center.ofBraided D).obj T) ((CategoryTheory.Center.ofBraided D).obj (Tᘁ))
      (Centre.positiveExactPairing T (Tᘁ))).f = η_ T (Tᘁ) := by
    change (ε F ≫ F.map (η_ T (Tᘁ)) ≫ δ F T (Tᘁ)).f = _
    simp [F]
  unfold positiveDualIso forgetDualIso rightDualIso rightAdjointMate
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_inv_f,
    CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.whiskerLeft_f,
    CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
    CategoryTheory.Center.id_f, hc]
  rfl

/-- The comparison between the double duals of an object and its positive lift. -/
def positiveDoubleDualIso (T : D) :
    (((CategoryTheory.Center.ofBraided D).obj T)ᘁ)ᘁ ≅
      (CategoryTheory.Center.ofBraided D).obj ((Tᘁ)ᘁ) :=
  Dimensions.rightDualIsoMap (positiveDualIso T).symm ≪≫ positiveDualIso (Tᘁ)

theorem positiveDualIso_inv_forget (T : D) :
    (positiveDualIso T).inv.f =
      (forgetDualIso ((CategoryTheory.Center.ofBraided D).obj T)).inv := by
  change ((CategoryTheory.Center.forget D).mapIso (positiveDualIso T)).inv = _
  exact (Iso.inv_eq_inv _ _).2 (positiveDualIso_forget T)

theorem positiveDoubleDualIso_forget (T : D) :
    (positiveDoubleDualIso T).hom.f =
      (forgetDoubleDualIso ((CategoryTheory.Center.ofBraided D).obj T)).hom := by
  let F := CategoryTheory.Center.ofBraided D
  let Z := F.obj T
  let e := positiveDualIso T
  have hnat := forgetDualIso_natural e.inv
  simp only [positiveDoubleDualIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, CategoryTheory.Center.comp_f, forgetDoubleDualIso]
  change (e.invᘁ).f ≫ (positiveDualIso (Tᘁ)).hom.f =
    (forgetDualIso (Zᘁ)).hom ≫ (forgetDualIso Z).invᘁ
  rw [positiveDualIso_forget]
  change (e.invᘁ).f ≫ (forgetDualIso (F.obj (Tᘁ))).hom = _
  change (e.invᘁ).f ≫ (forgetDualIso (F.obj (Tᘁ))).hom =
    (forgetDualIso (Zᘁ)).hom ≫ e.inv.fᘁ at hnat
  rw [hnat, positiveDualIso_inv_forget]

theorem positiveDoubleDualIso_inv_forget (T : D) :
    (positiveDoubleDualIso T).inv.f =
      (forgetDoubleDualIso ((CategoryTheory.Center.ofBraided D).obj T)).inv := by
  change ((CategoryTheory.Center.forget D).mapIso (positiveDoubleDualIso T)).inv = _
  exact (Iso.inv_eq_inv _ _).2 (positiveDoubleDualIso_forget T)

/-- The pivotal component transported to the positive centre lift. -/
def positivePivotalComponent (p : Dimensions.PivotalStructure (C := D)) (T : D) :
    (CategoryTheory.Center.ofBraided D).obj T ≅
      (((CategoryTheory.Center.ofBraided D).obj T)ᘁ)ᘁ :=
  (CategoryTheory.Center.ofBraided D).mapIso (p.iso T) ≪≫ (positiveDoubleDualIso T).symm

theorem positivePivotalComponent_forget (p : Dimensions.PivotalStructure (C := D)) (T : D) :
    (positivePivotalComponent p T).hom.f = (p.iso T).hom ≫
      (forgetDoubleDualIso ((CategoryTheory.Center.ofBraided D).obj T)).inv := by
  simp [positivePivotalComponent, positiveDoubleDualIso_inv_forget]

end PropertyF.Ground.CentreInduction

end

/-! Transfer a compatible pivotal structure to positive spherical centre data. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u})
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵" => CategoryTheory.Center C.Obj
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- The scalar of a centre unit endomorphism is unchanged by forgetting. -/
theorem center_unitScalar_forget (a : End (𝟙_ (𝒵))) :
    unitScalar 𝒵ᶠ a = unitScalar C (End.of a.asHom.f) := by
  apply (unit_algebraMap_bijective C).1
  rw [algebraMap_unitScalar]
  exact End.ext (congrArg (fun x : End (𝟙_ (𝒵)) => x.asHom.f)
    (algebraMap_unitScalar 𝒵ᶠ a))

/-- Compatible pivotal components have identical scalar dimensions after forgetting. -/
theorem center_pivotalDimension_forget
    {p : Dimensions.PivotalStructure (C := C.Obj)}
    {pZ : Dimensions.PivotalStructure (C := 𝒵)}
    {Z : 𝒵}
    (hcompat : PivotalCompatibleAt p pZ Z) :
    Dimensions.pivotalDimension 𝒵ᶠ pZ Z =
      Dimensions.pivotalDimension C p Z.1 := by
  simp only [Dimensions.pivotalDimension, center_unitScalar_forget,
    forget_trace_of_pivotal_component hcompat]

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {C : BraidedFusionCategory.{v,u}}
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵" => CategoryTheory.Center C.Obj
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- A compatible lift of a positive pivotal structure is spherical and has
FP dimensions on the centre. -/
theorem center_positive_spherical_of_compatible_pivotal
    {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p)
    {pZ : Dimensions.PivotalStructure (C := 𝒵)}
    (hcompat : ∀ Z : 𝒵, PivotalCompatibleAt p pZ Z) :
    pZ.IsSpherical ∧ PivotalHasFPDimensions 𝒵ᶠ pZ := by
  let D := 𝒵ᶠ
  have hd (i : Fin (rank D)) : Dimensions.pivotalDimension D pZ (simples D i) =
      (fpSimple D i : ℂ) := by
    rw [center_pivotalDimension_forget C (hcompat _),
      pivotalDimension_eq_fp hsimple]
    change (fpDimension C ((CategoryTheory.Center.forget C.Obj).obj (simples D i)) : ℂ) = _
    rw [Integrate.center_forget_fpDimension C, fpDimension_simple]
  refine ⟨?_, hd⟩
  apply (Dimensions.pivotal_spherical_iff_simple_dimensions_real D pZ).2
  intro i
  rw [hd]
  simp

end PropertyF.Ground.CentreInduction
