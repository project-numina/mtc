module
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.CentreInduction.PivotalTransfer
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.Dimensions.SphericalReal
public import PropertyF.Ground.CentreModular.InductionDimension

/-! Consequences of a pivotal structure compatible with centre forgetful. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- Forgetting an endomorphism of the unit preserves its scalar. -/
theorem center_forget_unitScalar (f : End (𝟙_ (CategoryTheory.Center C.Obj))) :
    unitScalar C (End.of f.asHom.f) = unitScalar (Integrate.bundledCenter C) f :=
  (CentreInduction.center_unitScalar_forget C f).symm

/-- A compatible pivotal component has the same dimension as its underlying object. -/
theorem center_pivotalDimension_eq_forget
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (Z : CategoryTheory.Center C.Obj)
    (hcompat : ((pZ.iso Z).hom.f) ≫ (CentreInduction.forgetDoubleDualIso C Z).hom =
      (p.iso Z.1).hom) :
    Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ Z =
      Dimensions.pivotalDimension C p Z.1 :=
  CentreInduction.center_pivotalDimension_forget C p pZ Z hcompat

/-- Compatibility with an FP-valued base pivotal structure forces the actual
centre pivotal dimensions to equal FP dimensions. -/
theorem center_pivotalDimension_eq_fp_of_compatible
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : ∀ Z, ((pZ.iso Z).hom.f) ≫ (CentreInduction.forgetDoubleDualIso C Z).hom =
      (p.iso Z.1).hom) (Z : CategoryTheory.Center C.Obj) :
    Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ Z =
      (fpDimension (Integrate.bundledCenter C) Z : ℂ) := by
  rw [center_pivotalDimension_eq_forget C p pZ Z (hcompat Z),
    CentreInduction.pivotalDimension_eq_fp C p hsimple]
  have h := Integrate.center_forget_fpDimension C Z
  change fpDimension C Z.1 = fpDimension (Integrate.bundledCenter C) Z at h
  exact congrArg (fun x : ℝ => (x : ℂ)) h

/-- The compatible centre pivotal structure is spherical without assuming
pseudo-unitarity of the centre. -/
theorem center_spherical_of_compatible
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : ∀ Z, ((pZ.iso Z).hom.f) ≫ (CentreInduction.forgetDoubleDualIso C Z).hom =
      (p.iso Z.1).hom) : pZ.IsSpherical := by
  apply (Dimensions.pivotal_spherical_iff_simple_dimensions_real (Integrate.bundledCenter C) pZ).2
  intro i
  rw [center_pivotalDimension_eq_fp_of_compatible C p hsimple pZ hcompat,
    fpDimension_simple]
  simp

/-- The categorical global dimension square follows from compatible pivotal
structures and the actual induction adjunction; centre pseudo-unitarity is a
consequence, not an assumption. -/
theorem center_globalDimension_square_of_compatible
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : ∀ Z, ((pZ.iso Z).hom.f) ≫ (CentreInduction.forgetDoubleDualIso C Z).hom =
      (p.iso Z.1).hom) :
    globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 := by
  apply center_globalDimension_of_adjunction C (CentreInduction.induction C)
    (CentreInduction.actualAdjunction C) (fun _ => ⟨Iso.refl _⟩) pZ
    (center_spherical_of_compatible C p hsimple pZ hcompat)
  intro i
  rw [center_pivotalDimension_eq_fp_of_compatible C p hsimple pZ hcompat, fpDimension_simple]

end PropertyF.Ground.CentreModular
