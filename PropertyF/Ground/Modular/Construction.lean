module
public import PropertyF.Ground.Modular.SSquare

/-!
# Modular data from an invertible categorical S matrix

The legacy `ModularData` compatibility bundle is constructed from a genuine
spherical category, real simple dimensions, and invertibility of its actual S
matrix. The separate Galois-action theorem avoids that legacy bundle.
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

/-- Construct the original modular-data bundle from the genuine S matrix, a
spherical pivotal structure, real simple dimensions, and S nondegeneracy. -/
def categoricalModularData (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j) :
    PropertyF.ModularData := by
  let N : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  exact modularDataOfVerlinde (rank C) (unitIndex C) (Ground.dualIndex C)
    (simpleDimension C p) (globalDimension C) (categoricalS C p)
    (simpleDimension_ne_zero C p) (globalDimension_ne_zero_of_invertibleS C p hp hdet hreal)
    (categorical_global_eq_sum_squares C p hp) (categoricalS_symmetric C p)
    (categoricalS_unit C p) (simpleDimension_unit C p) (categoricalS_square C p hp hdet hreal)
    N rfl (categoricalS_verlinde C p)

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
end PropertyF.Ground.Modular
