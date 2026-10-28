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
  apply End.ext
  change ((unitScalar 𝒵ᶠ a) • 𝟙 (𝟙_ (𝒵))).f = a.asHom.f
  exact congrArg (fun x : End (𝟙_ (𝒵)) => x.asHom.f) (algebraMap_unitScalar 𝒵ᶠ a)

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

/-- A compatible lift of a positive pivotal structure has the actual centre's
FP dimensions, is spherical, and proves the centre's pseudo-unitarity. -/
theorem center_positive_spherical_of_compatible_pivotal
    {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p)
    {pZ : Dimensions.PivotalStructure (C := 𝒵)}
    (hcompat : ∀ Z : 𝒵, PivotalCompatibleAt p pZ Z) :
    pZ.IsSpherical ∧
      PivotalHasFPDimensions 𝒵ᶠ pZ ∧
      PseudoUnitary 𝒵ᶠ := by
  let D := 𝒵ᶠ
  have hd (i : Fin (rank D)) : Dimensions.pivotalDimension D pZ (simples D i) =
      (fpSimple D i : ℂ) := by
    rw [center_pivotalDimension_forget C (hcompat _),
      pivotalDimension_eq_fp hsimple]
    change (fpDimension C ((CategoryTheory.Center.forget C.Obj).obj (simples D i)) : ℂ) = _
    rw [Integrate.center_forget_fpDimension C, fpDimension_simple]
  have hs : pZ.IsSpherical := by
    apply (Dimensions.pivotal_spherical_iff_simple_dimensions_real D pZ).2
    intro i
    rw [hd]
    simp
  exact ⟨hs, hd, Dimensions.positive_spherical_isPseudoUnitary D pZ hs (fpSimple D) hd
    (fpSimple_pos D)⟩

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {C : BraidedFusionCategory.{v,u}} [RigidCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵" => CategoryTheory.Center C.Obj
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- Positive pivotal data and the global-dimension square for the centre. -/
abbrev CenterPivotalData (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj)) : Prop :=
  pZ.IsSpherical ∧ PivotalHasFPDimensions (Integrate.bundledCenter C) pZ ∧
    PseudoUnitary (Integrate.bundledCenter C) ∧
    globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2

/-- A compatible pivotal lift supplies fusion, a positive spherical structure,
and the categorical global-dimension square without assuming centre pseudo-unitarity. -/
theorem center_structure_of_compatible_pivotal
    {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p)
    {pZ : Dimensions.PivotalStructure (C := 𝒵)}
    (hcompat : ∀ Z : 𝒵, PivotalCompatibleAt p pZ Z) :
    ∃ hFusion : IsFusionCategory (𝒵),
      letI := hFusion
      CenterPivotalData C pZ := by
  let J := (induction C).obj (𝟙_ C.Obj)
  let : IsFusionCategory (𝒵) :=
    center_fusion_of_compatible_pivotal C hsimple
      (forget_trace_of_pivotal_component (hcompat J))
  refine ⟨inferInstance, ?_⟩
  obtain ⟨hs, hd, hpu⟩ := center_positive_spherical_of_compatible_pivotal hsimple hcompat
  refine ⟨hs, hd, hpu, ?_⟩
  change globalDimension 𝒵ᶠ = _
  rw [show globalDimension 𝒵ᶠ =
      (globalFPDimension 𝒵ᶠ : ℂ) from hpu]
  rw [globalFPDimension_square_of_actual_induction C, Complex.ofReal_pow]

end PropertyF.Ground.CentreInduction
