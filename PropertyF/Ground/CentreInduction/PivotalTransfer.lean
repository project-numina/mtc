module
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.Dimensions.PivotalPseudoUnitary
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

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
