module
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GlobalInequality
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.DimensionNonzero
open scoped BigOperators

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

/-- Simple pivotal dimensions are nonzero, by rigidity, semisimplicity and Schur. -/
theorem pivotalDimension_simple_ne_zero (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C i) ≠ 0 := by
  have h := Ground.Modular.simpleDimension_ne_zero C p i
  simpa [Ground.Modular.simpleDimension, pivotalDimension, Ground.unitScalar_eq_equiv] using h

end PropertyF.Ground.Dimensions
