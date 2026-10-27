module
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

/-- A spherical structure with positive real simple dimensions is dual
invariant. This uses intrinsic norm invariance to remove the possible sign. -/
theorem spherical_dimension_dual_of_positive (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) :
    ∀ i, pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i) := by
  intro i
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  let : Simple (ᘁX) := Ground.simple_leftDual C X
  let : Simple (Xᘁ) := simple_rightDual C X
  let e : (ᘁX) ≅ (Xᘁ) :=
    leftDualIso HasLeftDual.exact (BraidedCategory.exactPairing_swap X (Xᘁ))
  obtain ⟨e'⟩ := Ground.dualIndex_iso C i
  let : Simple (Ground.simples C (Ground.dualIndex C i)) := Ground.simples_simple C _
  have hnorm : Ground.squaredNorm C (Ground.simples C (Ground.dualIndex C i)) =
      Ground.squaredNorm C X := by
    calc
      _ = Ground.squaredNorm C (Xᘁ) := target_squaredNorm_iso C (e'.symm ≪≫ e)
      _ = Ground.squaredNorm C X := target_squaredNorm_rightDual C X
  rw [target_squaredNorm_eq_dimension_sq C p hp, target_squaredNorm_eq_dimension_sq C p hp] at hnorm
  simp only [← rightTrace_id] at hnorm
  change pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) ^ 2 =
    pivotalDimension C p (Ground.simples C i) ^ 2 at hnorm
  rw [hreal, hreal, ← Complex.ofReal_pow, ← Complex.ofReal_pow] at hnorm
  have hsq : d (Ground.dualIndex C i) ^ 2 = d i ^ 2 := Complex.ofReal_injective hnorm
  have hd : d (Ground.dualIndex C i) = d i := by
    have h1 := hpos i
    have h2 := hpos (Ground.dualIndex C i)
    nlinarith
  rw [hreal, hreal, hd]

/-- Positive spherical simple dimensions imply the full Galois bounds needed
for the pseudo-unitary reduction. -/
theorem pseudoUnitary_galois_fp_bounds_of_positive (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) (hpu : Ground.PseudoUnitary C) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 0 < D ∧ D ≤ Ground.globalFPDimension C ∧
      σ (Ground.globalFPDimension C : ℂ) = (D : ℂ) :=
  pseudoUnitary_galois_fp_bounds_of_dual C p hp
    (spherical_dimension_dual_of_positive C p hp d hreal hpos) hpu σ

end PropertyF.Ground.Dimensions
