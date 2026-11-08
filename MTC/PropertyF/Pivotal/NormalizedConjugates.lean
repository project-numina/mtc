module
public import MTC.PropertyF.Pivotal.NormalizedScalarTwist
public import MTC.Center.Normalization.MugerIntegralOfPositive

/-! # Normalization of scalar twists from adjoint positivity -/

@[expose] public noncomputable section
open CategoryTheory MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions
open MTC.PropertyF.Reduction
namespace MTC.PropertyF.Pivotal
universe v u

/-- Under the manuscript's positivity hypothesis, there is one actual pivotal
structure whose scalar twists are normalized on all transparent simples. -/
theorem exists_normalized_scalarTwists_of_adjoint_positivity
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hpositive : PositiveOnTransparentAdjoint C p) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ (σ : ℂ ≃+* ℂ)
      (j : Fin (rank (ScalarTwist.category C σ))),
      MTC.Center.Transparent (simples (ScalarTwist.category C σ) j) →
      simpleDimension (ScalarTwist.category C σ) (ScalarTwist.pivotal C σ q) j =
        (fpSimple (ScalarTwist.category C σ) j : ℂ) := by
  obtain ⟨q, hq⟩ :=
    MTC.Center.Normalization.normalize_pivotal_on_muger_of_adjoint_positivity_unconditional
      C p hpositive
  refine ⟨q, fun σ j hj => normalized_transparent_scalarTwist C q σ hq ?_ j hj⟩
  intro i hi
  obtain ⟨n, hn⟩ := MTC.Center.Normalization.transparent_fpDimension_integer_of_adjoint_positivity
    C p hpositive (simples C i) hi
  exact ⟨n, (fpDimension_simple i).symm.trans hn⟩

end MTC.PropertyF.Pivotal
end
