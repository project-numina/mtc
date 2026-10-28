module
public import PropertyF.Ground.Dimensions.SphericalReal

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic norm is the product of the pivotal dimensions of a simple and its dual. -/
theorem squaredNorm_eq_pivotal_dimension_product (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    Ground.squaredNorm C (Ground.simples C i) = pivotalDimension C p (Ground.simples C i) *
      pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) := by
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  rw [target_squaredNorm_choice_independent C X (p.iso X), leftQuantumTrace_eq_rightDual]
  rw [← pivotal_dual p X, ← rightTrace_id, ← rightTrace_id]
  change pivotalDimension C p X * pivotalDimension C p (Xᘁ) = _
  rw [pivotalDimension_iso C p (rightDualLabelIso C i)]

/-- Each Galois-conjugate intrinsic norm is the squared norm of the corresponding conjugate pivotal dimension. -/
theorem galois_squaredNorm_eq_pivotalDimension_norm_sq (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    σ (Ground.squaredNorm C (Ground.simples C i)) =
      ((‖σ (pivotalDimension C p (Ground.simples C i))‖ ^ 2 : ℝ) : ℂ) := by
  rw [squaredNorm_eq_pivotal_dimension_product C p i, map_mul, galois_pivotalDimension_dual_eq_conj]
  simpa using Complex.mul_conj' (σ (pivotalDimension C p (Ground.simples C i)))

end PropertyF.Ground.Dimensions
