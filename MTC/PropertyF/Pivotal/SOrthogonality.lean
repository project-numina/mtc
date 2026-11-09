module
public import MTC.Modular.SSquare
public import MTC.PropertyF.Pivotal.FPObject

/-!
# Orthogonality for arbitrary pivotal dimensions

The categorical S matrix has orthogonal columns as soon as it is invertible.
No reality or sphericality hypothesis is used.
-/

@[expose] public noncomputable section
open MTC.Fusion MTC.Modular
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj))

/-- Distinct columns of an invertible categorical S matrix are Hermitian
orthogonal, for an arbitrary pivotal structure. -/
theorem categoricalS_columns_orthogonal
    (hdet : (categoricalS C p).det ≠ 0) {a b : Fin (rank C)} (hab : a ≠ b) :
    ∑ x, starRingEnd ℂ (categoricalS C p x a) * categoricalS C p x b = 0 :=
  character_columns_orthogonal_general ⟨unitIndex C, fusionCoeff C⟩ (dualIndex C)
    (fun i j k ↦ fusionCoeff_dual_symmetry C i k j)
    (categoricalSCharacter C p) (fun _ _ ↦ rfl) hdet
    (simpleDimension_ne_zero C p) hab

/-- If a matrix commutes with a diagonal matrix, a nonzero matrix entry
forces the corresponding diagonal entries to agree. -/
theorem diagonal_eq_of_commute {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (S : Matrix ι ι K) (d : ι → K) {x u : ι}
    (hcomm : Matrix.diagonal d * S = S * Matrix.diagonal d)
    (hxu : S x u ≠ 0) : d x = d u := by
  have h := congrArg (fun M : Matrix ι ι K ↦ M x u) hcomm
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  exact mul_right_cancel₀ hxu (by simpa only [mul_comm] using h)

/-- The diagonal matrix of Hermitian column lengths commutes with a
symmetric matrix whose distinct columns are orthogonal. -/
theorem symmetric_orthogonal_gram_commutes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℂ) (hsym : ∀ x y, S x y = S y x)
    (horth : ∀ {a b}, a ≠ b → ∑ z, starRingEnd ℂ (S z a) * S z b = 0) :
    Matrix.diagonal (fun x ↦ ∑ z, starRingEnd ℂ (S z x) * S z x) * S =
      S * Matrix.diagonal (fun x ↦ ∑ z, starRingEnd ℂ (S z x) * S z x) := by
  let A : Matrix ι ι ℂ := fun x y ↦ starRingEnd ℂ (S y x)
  let d : ι → ℂ := fun x ↦ ∑ z, starRingEnd ℂ (S z x) * S z x
  have hgram : A * S = Matrix.diagonal d := by
    ext a b
    rw [Matrix.mul_apply]
    by_cases h : a = b
    · subst b
      simp [A, d]
    · simp [A, Matrix.diagonal_apply_ne _ h, horth h]
  have hreverse : S * A = Matrix.diagonal d := by
    ext a b
    rw [Matrix.mul_apply]
    by_cases h : a = b
    · subst b
      simp [A, d, hsym, mul_comm]
    · have hz : (∑ z, S a z * starRingEnd ℂ (S b z)) = 0 := by
        simpa only [hsym, mul_comm] using horth (a := b) (b := a) (Ne.symm h)
      simp [A, Matrix.diagonal_apply_ne _ h, hz]
  calc
    _ = (S * A) * S := congrArg (fun M ↦ M * S) hreverse.symm
    _ = S * (A * S) := Matrix.mul_assoc _ _ _
    _ = _ := congrArg (fun M ↦ S * M) hgram

/-- A symmetric matrix with orthogonal columns and a nonzero distinguished
column has equal squared Hermitian lengths in every column. -/
theorem symmetric_orthogonal_columns_equal_length
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ) (u : ι)
    (hsym : ∀ x y, S x y = S y x) (hne : ∀ x, S x u ≠ 0)
    (horth : ∀ {a b}, a ≠ b → ∑ z, starRingEnd ℂ (S z a) * S z b = 0)
    (x : ι) :
    (∑ z, starRingEnd ℂ (S z x) * S z x) =
      ∑ z, starRingEnd ℂ (S z u) * S z u :=
  diagonal_eq_of_commute S _ (symmetric_orthogonal_gram_commutes S hsym horth) (hne x)

/-- Every categorical S column has the same Hermitian norm, without assuming
sphericality or real pivotal dimensions. -/
theorem categoricalS_column_length (hdet : (categoricalS C p).det ≠ 0)
    (x : Fin (rank C)) :
    (∑ z, starRingEnd ℂ (categoricalS C p z x) * categoricalS C p z x) =
      ∑ z, starRingEnd ℂ (simpleDimension C p z) * simpleDimension C p z := by
  have h := symmetric_orthogonal_columns_equal_length (categoricalS C p) (unitIndex C)
    (categoricalS_symmetric C p)
    (fun i ↦ by rw [categoricalS_unit]; exact simpleDimension_ne_zero C p i)
    (fun {a b} h ↦ categoricalS_columns_orthogonal C p hdet (a := a) (b := b) h) x
  simpa only [categoricalS_unit] using h

/-- The FP column gives the norm identity in terms of simple pivotal
 dimensions, with no positivity or sphericality assumption. -/
theorem fp_column_dimension_identity (hdet : (categoricalS C p).det ≠ 0) :
    ∃ j : Fin (rank C),
      (∀ i, categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ)) ∧
      (∑ i, starRingEnd ℂ (simpleDimension C p i) * simpleDimension C p i) =
        (starRingEnd ℂ (simpleDimension C p j) * simpleDimension C p j) *
          (globalFPDimension C : ℂ) := by
  obtain ⟨j, hj, _⟩ := existsUnique_fp_column C p hdet
  refine ⟨j, hj, ?_⟩
  rw [← categoricalS_column_length C p hdet j]
  exact fp_proportional_column_gram C _ _ hj

end MTC.PropertyF.Pivotal
