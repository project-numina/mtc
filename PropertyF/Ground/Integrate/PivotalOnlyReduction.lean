module
public import PropertyF.Ground.Integrate.RigidCenterReduction
public import PropertyF.Ground.CentreInduction.PivotalCentrality

/-! Centre fusion and sphericality from any base pivotal structure. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- The fusion instance constructed from a pivotal pseudo-unitary base. -/
@[instance_reducible] def centerFusionOfPivotalPseudoUnitary
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hpu : PseudoUnitary C) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  exact Classical.choose (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu)

/-- The actual centre spherical pivotal structure constructed along the same route. -/
def centerPivotalOfPivotalPseudoUnitary
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hpu : PseudoUnitary C) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj) := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  exact Classical.choose (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))

/-- With centre rigidity, fusion and positive sphericality constructed, the
remaining centre conditions are S-invertibility and numerical-core integrality.
Existence of a base pivotal structure is still an explicit premise. -/
theorem target_of_pivotal_base_and_integral_numerical_core
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        (Modular.categoricalS D pZ).det ≠ 0 ∧
        (∀ y ∈ numericalProductCore C pZ,
          ∃ z : ℤ, Modular.simpleDimension D pZ y = z)) : TargetStatement.{v,u} := by
  apply target_of_fusion_center_integral_numerical_core
  intro C hpu hF
  obtain ⟨p, hdet, hintegral⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))
  obtain ⟨hspherical, hd, _, _⟩ := hs
  change ∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
    (simples (Integrate.bundledCenter C) i) = (fpSimple (Integrate.bundledCenter C) i : ℂ) at hd
  refine ⟨inferInstance, pZ, hspherical, ?_, hdet, hintegral⟩
  intro i
  simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
    Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hd i

end PropertyF.Ground
