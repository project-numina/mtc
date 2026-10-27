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

/-- A positive spherical structure supplies the Galois bounds; the
pseudo-unitarity equation and dual invariance follow from positivity. -/
theorem positive_spherical_galois_fp_bounds (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 0 < D ∧ D ≤ Ground.globalFPDimension C ∧
      σ (Ground.globalFPDimension C : ℂ) = (D : ℂ) :=
  pseudoUnitary_galois_fp_bounds_of_positive C p hp d hreal hpos
    (positive_spherical_isPseudoUnitary C p hp d hreal hpos) σ

end PropertyF.Ground.Dimensions
