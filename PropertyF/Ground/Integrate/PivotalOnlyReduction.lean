module
public import PropertyF.Ground.Integrate.CenterSquareReduction
public import PropertyF.Ground.CentreInduction.PivotalTransfer
public import PropertyF.Ground.Centre.Rigid
public import PropertyF.Ground.CentreInduction.ForgetDual
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

end PropertyF.Ground
