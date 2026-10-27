module
public import PropertyF.Ground.Modular.SSquare

/-!
# Galois symmetry from an invertible categorical S matrix

A spherical category with real simple dimensions and an invertible S matrix
has the Galois symmetries of its normalized S columns.
-/
open scoped BigOperators
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular

/-- Invertibility and S-square force the global dimension to be nonzero. -/
theorem globalDimension_ne_zero_of_invertibleS (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j) :
    globalDimension C ≠ 0 := by
  classical
  let _ : Nonempty (Fin (rank C)) := ⟨unitIndex C⟩
  intro hz
  have hs : categoricalS C p * categoricalS C p = 0 := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.zero_apply, categoricalS_square C p hp hdet hreal, hz]
    split_ifs <;> rfl
  have hh := congrArg Matrix.det hs
  rw [Matrix.det_mul] at hh
  simp only [Matrix.det_zero] at hh
  exact mul_ne_zero hdet hdet hh

/-- The S-column Galois action for any nondegenerate spherical category with
real simple dimensions, without old input bundles. -/
theorem categoricalS_galois_action_of_invertibleS (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)), ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (categoricalS C p i j / simpleDimension C p j) =
        categoricalS C p i (act σ j) / simpleDimension C p (act σ j) :=
  categoricalS_galois_action C p (Ground.dualIndex C)
    (globalDimension_ne_zero_of_invertibleS C p hp hdet hreal)
    (categoricalS_square C p hp hdet hreal) (categoricalS_verlinde C p)
/-- Proposition 2.1 for the actual categorical S matrix, together with the
full complex-automorphism action from which it is derived. -/
theorem categoricalS_galois_symmetry (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)),
      (∀ (σ : ℂ ≃+* ℂ) i j,
        σ (categoricalS C p i j / simpleDimension C p j) =
          categoricalS C p i (act σ j) / simpleDimension C p (act σ j)) ∧
      (∀ (σ : ℂ ≃+* ℂ) i,
        categoricalS C p i (act σ (unitIndex C)) =
          simpleDimension C p (act σ (unitIndex C)) * σ (simpleDimension C p i)) ∧
      (∀ (σ : ℂ ≃+* ℂ), act σ (unitIndex C) = Ground.dualIndex C (act σ (unitIndex C))) ∧
      (∀ (σ : ℂ ≃+* ℂ), σ (globalDimension C) =
        globalDimension C / simpleDimension C p (act σ (unitIndex C)) ^ 2) := by
  obtain ⟨act, hact⟩ := categoricalS_galois_action_of_invertibleS C p hp hdet hreal
  have hprop (σ : ℂ ≃+* ℂ) := galois_unit_properties (unitIndex C) (categoricalS C p)
    (Ground.dualIndex C) (simpleDimension C p) (globalDimension C) (simpleDimension_ne_zero C p)
    (globalDimension_ne_zero_of_invertibleS C p hp hdet hreal) (simpleDimension_unit C p)
    (categorical_global_eq_sum_squares C p hp) (categoricalS_symmetric C p)
    (categoricalS_unit C p) (categoricalS_square C p hp hdet hreal) σ
    (act σ (unitIndex C)) (fun x => hact σ x (unitIndex C))
  exact ⟨act, hact, fun σ => (hprop σ).1, fun σ => (hprop σ).2.1, fun σ => (hprop σ).2.2⟩
end PropertyF.Ground.Modular
