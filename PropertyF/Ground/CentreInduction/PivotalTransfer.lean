module
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.Dimensions.PivotalPseudoUnitary
public import PropertyF.Ground.Dimensions.PositiveCanonical

/-! Transfer a compatible pivotal structure to positive spherical centre data. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u})
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- The scalar of a centre unit endomorphism is unchanged by forgetting. -/
theorem center_unitScalar_forget (a : End (𝟙_ (CategoryTheory.Center C.Obj))) :
    unitScalar (Integrate.bundledCenter C) a = unitScalar C (End.of a.asHom.f) := by
  let z := unitScalar (Integrate.bundledCenter C) a
  have h := algebraMap_unitScalar (Integrate.bundledCenter C) a
  have hf := congrArg (fun x : End (𝟙_ (CategoryTheory.Center C.Obj)) => x.asHom.f) h
  have hb : End.of a.asHom.f = algebraMap ℂ (End (𝟙_ C.Obj)) z := by
    apply End.ext
    change a.asHom.f = z • 𝟙 (𝟙_ C.Obj)
    change (z • 𝟙 (𝟙_ (CategoryTheory.Center C.Obj))).f = a.asHom.f at hf
    exact hf.symm
  change z = unitScalar C (End.of a.asHom.f)
  rw [hb, unitScalar_algebraMap]

/-- Compatible pivotal components have identical scalar dimensions after forgetting. -/
theorem center_pivotalDimension_forget
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (Z : CategoryTheory.Center C.Obj)
    (hcompat : (pZ.iso Z).hom.f ≫ (forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom) :
    Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ Z =
      Dimensions.pivotalDimension C p Z.1 := by
  unfold Dimensions.pivotalDimension
  rw [center_unitScalar_forget]
  rw [forget_trace_of_pivotal_component C p pZ Z hcompat]

/-- A compatible lift of a positive pivotal structure has the actual centre's
FP dimensions, is spherical, and proves the centre's pseudo-unitarity. -/
theorem center_positive_spherical_of_compatible_pivotal
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : ∀ Z : CategoryTheory.Center C.Obj,
      (pZ.iso Z).hom.f ≫ (forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom) :
    pZ.IsSpherical ∧
      (∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
        (simples (Integrate.bundledCenter C) i) =
          (fpSimple (Integrate.bundledCenter C) i : ℂ)) ∧
      PseudoUnitary (Integrate.bundledCenter C) := by
  let D := Integrate.bundledCenter C
  have hd (i : Fin (rank D)) : Dimensions.pivotalDimension D pZ (simples D i) =
      (fpSimple D i : ℂ) := by
    rw [center_pivotalDimension_forget C p pZ _ (hcompat _),
      pivotalDimension_eq_fp C p hsimple]
    have hf := Integrate.center_forget_fpDimension C (simples D i)
    change fpDimension C (simples D i).1 = fpDimension D (simples D i) at hf
    rw [hf, fpDimension_simple]
  have hs : pZ.IsSpherical := by
    apply (Dimensions.pivotal_spherical_iff_simple_dimensions_real D pZ).2
    intro i
    rw [hd]
    simp
  refine ⟨hs, hd, ?_⟩
  apply Dimensions.positive_spherical_isPseudoUnitary D pZ hs (fpSimple D)
  · exact hd
  · exact fpSimple_pos D

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

/-- A compatible pivotal lift supplies fusion, a positive spherical structure,
and the categorical global-dimension square without assuming centre pseudo-unitarity. -/
theorem center_structure_of_compatible_pivotal
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : ∀ Z : CategoryTheory.Center C.Obj,
      (pZ.iso Z).hom.f ≫ (forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom) :
    ∃ hFusion : IsFusionCategory (CategoryTheory.Center C.Obj),
      letI := hFusion
      pZ.IsSpherical ∧
      (∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
        (simples (Integrate.bundledCenter C) i) =
          (fpSimple (Integrate.bundledCenter C) i : ℂ)) ∧
      PseudoUnitary (Integrate.bundledCenter C) ∧
      globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 := by
  let J := (induction C).obj (𝟙_ C.Obj)
  let : IsFusionCategory (CategoryTheory.Center C.Obj) :=
    center_fusion_of_compatible_pivotal C p hsimple pZ
      (forget_trace_of_pivotal_component C p pZ J (hcompat J))
  refine ⟨inferInstance, ?_⟩
  obtain ⟨hs, hd, hpu⟩ := center_positive_spherical_of_compatible_pivotal C p hsimple pZ hcompat
  refine ⟨hs, hd, hpu, ?_⟩
  change globalDimension (Integrate.bundledCenter C) = _
  rw [show globalDimension (Integrate.bundledCenter C) =
      (globalFPDimension (Integrate.bundledCenter C) : ℂ) from hpu]
  rw [globalFPDimension_square_of_actual_induction C, Complex.ofReal_pow]

end PropertyF.Ground.CentreInduction
