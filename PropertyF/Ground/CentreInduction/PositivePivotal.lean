module
public import PropertyF.Ground.CentreInduction.ForgetDualTensor
public import PropertyF.Ground.CentreInduction.FiniteSimples
public import PropertyF.Ground.Dimensions.DoubleDualPairing
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix

open PropertyF.Ground.Dimensions

/-! # Pivotal structures on the centre

Compatible pivotal components lift to the centre. When the base pivotal dimensions agree with
Frobenius–Perron dimensions, they also yield centre fusion and a positive spherical structure.
-/

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵ᶜ" => Center C.Obj

variable {C} in
/-- A pivotal structure has the Frobenius–Perron dimensions on simple objects. -/
abbrev PivotalHasFPDimensions (p : PivotalStructure (C := C.Obj)) : Prop :=
  ∀ i, pivotalDimension C p (simples C i) = (fpSimple C i : ℂ)


variable {p : PivotalStructure (C := C.Obj)}

variable {C} in
/-- A compatible centre pivotal structure constructs centre fusion when the base
pivotal dimensions equal FP dimensions. -/
theorem center_fusion_of_compatible_pivotal (hsimple : PivotalHasFPDimensions p) [RigidCategory 𝒵ᶜ]
    {pZ : PivotalStructure (C := 𝒵ᶜ)}
    (hcompat : PivotalCompatibleAt p pZ ((induction C).obj (𝟙_ C.Obj))) : IsFusionCategory 𝒵ᶜ :=
  center_fusion_of_nonzero_induced_trace pZ fun hz => by
    have ht := forget_trace_of_pivotal_component hcompat (𝟙 _)
    change (pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj)))).asHom.f =
      (p.rightTrace (𝟙 (underlying (𝟙_ C.Obj)))).asHom at ht
    have hd : pivotalDimension C p (underlying (𝟙_ C.Obj)) = (globalFPDimension C : ℂ) := by
      rw [pivotalDimension_eq_fp hsimple, fpDimension_underlying, fpDimension_unit, mul_one]
    change unitScalar C (p.rightTrace (𝟙 (underlying (𝟙_ C.Obj)))) = _ at hd
    rw [show p.rightTrace (𝟙 (underlying (𝟙_ C.Obj))) = 0 from
      End.ext (ht.symm.trans (congrArg (fun a => a.asHom.f) hz))] at hd
    exact (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))) <|
        by simpa only [Ground.unitScalar_eq_equiv, map_zero] using hd.symm

end PropertyF.Ground.CentreInduction

end
end

section
/-! Lift a pivotal structure once its transported components are central. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RightRigidCategory (Center D)]
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
  iso Z := Center.isoMk ⟨transportedPivotalHom p Z, hc Z⟩
  naturality f := Center.ext _ _ (by
    simpa only [Center.comp_f, Center.isoMk_hom] using transported_pivotal_natural p f)
  tensor X Y := Center.ext _ _ (by
    simpa only [Center.comp_f, Center.tensor_f, Center.isoMk_hom, Center.tensor_fst] using
      (transported_pivotal_tensor p X Y).symm)
  unit := Center.ext _ _ (transported_pivotal_unit p)

variable {p} in
/-- The lifted component agrees with the original pivotal component. -/
theorem liftedPivotalStructure_compatible
    (hc : PivotalComponentsCentral p) (Z : 𝒵) :
    PivotalCompatibleAt p (liftedPivotalStructure p hc) Z := by
  simp [PivotalCompatibleAt, liftedPivotalStructure, transportedPivotalHom]

end

end PropertyF.Ground.CentreInduction

end
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

variable {C} in
/-- The scalar of a centre unit endomorphism is unchanged by forgetting. -/
theorem center_unitScalar_forget (a : End (𝟙_ (𝒵))) :
    unitScalar 𝒵ᶠ a = unitScalar C (End.of a.asHom.f) :=
  (unit_algebraMap_bijective C).1 <|
    (End.ext (congrArg (fun x : End (𝟙_ (𝒵)) => x.asHom.f)
      (algebraMap_unitScalar 𝒵ᶠ a))).trans (algebraMap_unitScalar C _).symm

variable {C} in
/-- Compatible pivotal components have identical scalar dimensions after forgetting. -/
theorem center_pivotalDimension_forget
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := 𝒵)} {Z : 𝒵}
    (hcompat : PivotalCompatibleAt p pZ Z) :
    pivotalDimension 𝒵ᶠ pZ Z = pivotalDimension C p Z.1 :=
  (center_unitScalar_forget (pZ.rightTrace (𝟙 Z))).trans
    (congrArg (fun f => unitScalar C (End.of f)) (forget_trace_of_pivotal_component hcompat (𝟙 Z)))

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
    {p : PivotalStructure (C := C.Obj)} (hsimple : PivotalHasFPDimensions p)
    {pZ : PivotalStructure (C := 𝒵)} (hcompat : ∀ Z : 𝒵, PivotalCompatibleAt p pZ Z) :
    pZ.IsSpherical ∧ PivotalHasFPDimensions (C := 𝒵ᶠ) pZ :=
  let D := 𝒵ᶠ
  let hd (i : Fin (rank D)) : pivotalDimension D pZ (simples D i) =
      (fpSimple D i : ℂ) := by
    rw [center_pivotalDimension_forget (hcompat _), pivotalDimension_eq_fp hsimple,
      Integrate.center_forget_fpDimension C, fpDimension_simple]
  ⟨(pivotal_spherical_iff_simple_dimensions_real D pZ).2 (fun i ↦ by simp [hd i]), hd⟩

end PropertyF.Ground.CentreInduction
