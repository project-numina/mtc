module
public import PropertyF.Ground.Dimensions.PivotalPairing

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- Real pivotal simple dimensions are invariant under duality. -/
theorem pivotalDimension_dual_of_real (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i) := by
  have h := galois_pivotalDimension_dual_eq_conj C p (RingEquiv.refl ℂ) i
  change pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
    star (pivotalDimension C p (Ground.simples C i)) at h
  simpa [hreal] using h

/-- In a real spherical category, all Galois conjugates of simple squared
norms are positive and bounded by the corresponding FP square. -/
theorem real_spherical_squaredNorm_galois_bounds (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Ground.fpSimple C i ^ 2 ∧
      σ (Ground.squaredNorm C (Ground.simples C i)) = (r : ℂ) := by
  obtain ⟨r, hr, he⟩ := spherical_squaredNorm_totallyPositive_of_dual C p hp
    (pivotalDimension_dual_of_real C p d hreal) σ i
  refine ⟨r, hr, ?_, he⟩
  have hb := spherical_squaredNorm_galois_norm_le_fp_sq C p hp σ i
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hb
  exact hb

/-- In a real spherical category, every Galois conjugate of the categorical
global dimension lies between one and the global FP dimension. -/
theorem real_spherical_globalDimension_galois_bounds (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 1 ≤ D ∧ D ≤ Ground.globalFPDimension C ∧ σ (Ground.globalDimension C) = (D : ℂ) :=
  spherical_globalDimension_galois_bounds_of_dual C p hp
    (pivotalDimension_dual_of_real C p d hreal) σ
end PropertyF.Ground.Dimensions
