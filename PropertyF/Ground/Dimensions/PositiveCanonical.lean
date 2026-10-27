module
public import PropertyF.Ground.Dimensions.PivotalUniqueness
public import PropertyF.Ground.Dimensions.PositiveSpherical

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- A positive spherical structure forces pseudo-unitarity. -/
theorem positive_spherical_isPseudoUnitary (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) : Ground.PseudoUnitary C := by
  have hfp := positive_pivotalDimension_eq_fpSimple C p d hreal hpos
  unfold Ground.PseudoUnitary Ground.globalFPDimension
  rw [target_globalDimension_eq_sum_squares C p hp]
  simp only [← rightTrace_id, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  change pivotalDimension C p (Ground.simples C i) ^ 2 = ((Ground.fpSimple C i : ℝ) : ℂ) ^ 2
  rw [hreal, hfp]

end PropertyF.Ground.Dimensions
