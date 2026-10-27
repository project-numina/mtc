module
public import PropertyF.Ground.CentreInduction.DrinfeldFourth
public import PropertyF.Ground.CentreIntegrate.TwistBalancing
public import PropertyF.Ground.Dimensions.MonodromyTensorCap

/-! The Drinfeld tensor law and its pseudo-unitary consequences. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The canonical Drinfeld isomorphism satisfies its tensor law. -/
theorem drinfeldTensorLaw (C : BraidedFusionCategory.{v,u}) : DrinfeldTensorLaw C := by
  intro X Y
  exact CentreIntegrate.drinfeld_tensor_of_pairing_cap C X Y
    (Dimensions.drinfeld_tensor_pairing_cap C X Y)


/-- Every pseudo-unitary braided fusion category has a positive spherical
structure with its actual FP dimensions, without any pivotal premise. -/
theorem positive_spherical_of_pseudoUnitary (C : BraidedFusionCategory.{v,u})
    (hpu : PseudoUnitary C) :
    ∃ p : Dimensions.PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) :=
  positive_spherical_of_drinfeld_tensor C (drinfeldTensorLaw C) hpu

end PropertyF.Ground.CentreInduction
