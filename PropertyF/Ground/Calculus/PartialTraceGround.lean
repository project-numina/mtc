module
public import PropertyF.Ground.Dimensions.IteratedTrace
public import PropertyF.Ground.Modular.DimensionNonzero

/-! Simple-strand partial trace from the constructed iterated trace law. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

/-- In a genuine braided fusion category, the partial trace onto a simple
surviving object is the total trace divided by its nonzero pivotal dimension. -/
theorem rightPartialTrace_simple_ground (C : Ground.BraidedFusionCategory.{v,u})
    (X Y : C.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (f : End (X ⊗ Y)) :
    rightPartialTrace p X Y f =
      (scalar (p.rightTrace f.asHom) / scalar (p.rightTrace (𝟙 X))) • (1 : End X) := by
  let _ : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  apply rightPartialTrace_simple_of_trace_compatibility X Y p scalar f
  · intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply scalar.injective
    simpa using h
  · exact Dimensions.rightTrace_partialTrace p X Y f

end PropertyF.Ground.Calculus
