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
    ∑ x, starRingEnd ℂ (categoricalS C p x a) * categoricalS C p x b = 0 := by
  let cols := categoricalSCharacter C p
  have hne : cols a ≠ cols b := fun h ↦
    hab (normalized_columns_injective (simpleDimension_ne_zero C p) hdet (by
      funext i
      simpa only [cols, categoricalSCharacter, normalizedSColumn] using
        congrFun (congrArg Character.value h) i))
  have h := character_orthogonal ⟨unitIndex C, fusionCoeff C⟩ (dualIndex C)
    (fun i j k ↦ fusionCoeff_dual_symmetry C i k j) (cols a) (cols b) hne
  have hdiv : (∑ x, starRingEnd ℂ (categoricalS C p x a) * categoricalS C p x b) /
      (starRingEnd ℂ (simpleDimension C p a) * simpleDimension C p b) = 0 := by
    simpa only [cols, categoricalSCharacter, normalizedSColumn, map_div₀,
      div_mul_div_comm, ← Finset.sum_div] using h
  exact (div_eq_zero_iff.mp hdiv).resolve_right
    (mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 (simpleDimension_ne_zero C p a))
      (simpleDimension_ne_zero C p b))

/-- A symmetric matrix with orthogonal columns and a nonzero distinguished
column has equal squared Hermitian lengths in every column. -/
theorem symmetric_orthogonal_columns_equal_length
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ) (u : ι)
    (hsym : ∀ x y, S x y = S y x) (hne : ∀ x, S x u ≠ 0)
    (horth : ∀ {a b}, a ≠ b → ∑ z, starRingEnd ℂ (S z a) * S z b = 0)
    (x : ι) :
    (∑ z, starRingEnd ℂ (S z x) * S z x) =
      ∑ z, starRingEnd ℂ (S z u) * S z u := by
  let A : Matrix ι ι ℂ := fun x y ↦ starRingEnd ℂ (S y x)
  have hleft (x t : ι) (h : x ≠ t) : (S * A) x t = 0 := by
    simp only [Matrix.mul_apply]
    simpa only [A, hsym, mul_comm] using horth (a := t) (b := x) (Ne.symm h)
  have hright (t : ι) (h : t ≠ u) : (A * S) t u = 0 := by
    change (∑ z, starRingEnd ℂ (S z t) * S z u) = 0
    exact horth h
  have heq := congrArg (fun M : Matrix ι ι ℂ ↦ M x u) (Matrix.mul_assoc S A S)
  simp only [Matrix.mul_apply] at heq
  have hl : (∑ t, (∑ z, S x z * A z t) * S t u) =
      (∑ z, starRingEnd ℂ (S z x) * S z x) * S x u := by
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)]
    · simp only [A, hsym, mul_comm]
    · intro t _ ht
      change (S * A) x t * S t u = 0
      rw [hleft x t (Ne.symm ht), zero_mul]
  have hr : (∑ t, S x t * (∑ z, A t z * S z u)) =
      S x u * (∑ z, starRingEnd ℂ (S z u) * S z u) := by
    rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]
    intro t _ ht
    change S x t * (A * S) t u = 0
    rw [hright t ht, mul_zero]
  rw [hl, hr] at heq
  exact mul_right_cancel₀ (hne x) (by simpa only [mul_comm] using heq)

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
  have h := (categoricalS_column_length C p hdet j).symm
  rw [h]
  simp only [hj, map_mul, Complex.conj_ofReal,
    globalFPDimension, Complex.ofReal_sum, Complex.ofReal_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end MTC.PropertyF.Pivotal
