module
public import PropertyF.Ground.Dimensions.PivotalUniqueness
public import PropertyF.Ground.Dimensions.PositiveSpherical

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- Under a positive spherical structure, each intrinsic simple squared norm
is the square of its FP dimension. -/
theorem positive_spherical_squaredNorm_eq_fp_sq (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) (i : Fin (Ground.rank C)) :
    Ground.squaredNorm C (Ground.simples C i) = ((Ground.fpSimple C i ^ 2 : ℝ) : ℂ) := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  rw [target_squaredNorm_eq_dimension_sq C p hp, ← rightTrace_id]
  change pivotalDimension C p (Ground.simples C i) ^ 2 = _
  rw [hreal, positive_pivotalDimension_eq_fpSimple C p d hreal hpos, Complex.ofReal_pow]

/-- In a positive spherical category all conjugates of intrinsic simple norms
are positive real numbers. -/
theorem positive_spherical_squaredNorm_totallyPositive (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ∃ r : ℝ, 0 < r ∧ σ (Ground.squaredNorm C (Ground.simples C i)) = (r : ℂ) :=
  spherical_squaredNorm_totallyPositive_of_dual C p hp
    (spherical_dimension_dual_of_positive C p hp d hreal hpos) σ i

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
