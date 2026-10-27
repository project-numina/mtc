module
public import PropertyF.Ground.Integrate.NumericalCoreReduction
public import PropertyF.Ground.CentreInduction.PivotalTransfer

/-! A compatible pivotal lift also constructs centre fusion and its sphere. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- Centre fusion is supplied by a compatible lift of an FP-valued base
pivotal structure. -/
@[instance_reducible] def compatibleCenterFusion
    (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : ∀ Z : CategoryTheory.Center C.Obj,
      (pZ.iso Z).hom.f ≫ (CentreInduction.forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom) :
    IsFusionCategory (CategoryTheory.Center C.Obj) :=
  Classical.choose (CentreInduction.center_structure_of_compatible_pivotal C p hsimple pZ hcompat)

/-- A compatible lift replaces separate centre fusion and spherical-existence
premises. Its existence, numerical core integrality, and modularity remain
explicit assumptions. -/
theorem target_of_compatible_center_and_integral_numerical_core
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
      ∃ (hR : RigidCategory (CategoryTheory.Center C.Obj)),
        letI := hR
        ∃ (p : Dimensions.PivotalStructure (C := C.Obj))
          (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
          (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
          (hcompat : ∀ Z : CategoryTheory.Center C.Obj,
            (pZ.iso Z).hom.f ≫ (CentreInduction.forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom),
          letI := compatibleCenterFusion C p hsimple pZ hcompat
          let D := Integrate.bundledCenter C
          (Modular.categoricalS D pZ).det ≠ 0 ∧
          (∀ y ∈ numericalProductCore C pZ,
            ∃ z : ℤ, Modular.simpleDimension D pZ y = z)) : TargetStatement.{v,u} := by
  apply target_of_integral_numerical_center_core
  intro C hPU hF
  obtain ⟨hR, p, hsimple, pZ, hcompat, hdet, hintegral⟩ := hCenter C hPU hF
  letI := hR
  letI := compatibleCenterFusion C p hsimple pZ hcompat
  have hstructure := Classical.choose_spec
    (CentreInduction.center_structure_of_compatible_pivotal C p hsimple pZ hcompat)
  obtain ⟨hspherical, hd, _, _⟩ := hstructure
  refine ⟨hR, inferInstance, pZ, hspherical, ?_, hdet, hintegral⟩
  intro i
  simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
    Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hd i

end PropertyF.Ground
