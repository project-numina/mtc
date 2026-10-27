module
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! The algebraic consequence of a nonsingular system of integer exponent
relations, as used in Vafa-type finiteness arguments. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling

/-- A solution in an arbitrary abelian group of homogeneous integer relations
is annihilated by the determinant of the coefficient matrix. -/
theorem det_zsmul_eq_zero_of_relations {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommGroup A] (M : Matrix ι ι ℤ) (x : ι → A)
    (h : ∀ i, ∑ j, M i j • x j = 0) (i : ι) : M.det • x i = 0 := by
  classical
  have hzero : (∑ k, M.adjugate i k • (∑ j, M k j • x j)) = 0 := by
    simp [h]
  have hchange : (∑ k, M.adjugate i k • (∑ j, M k j • x j)) =
      ∑ j, (∑ k, M.adjugate i k * M k j) • x j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  rw [hchange] at hzero
  have hadj := Matrix.adjugate_mul M
  have hentry := congrFun (congrFun hadj i) 
  have hm : ∀ j, (∑ k, M.adjugate i k * M k j) = if i = j then M.det else 0 := by
    intro j
    have h := hentry j
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using h
  simpa [hm, eq_comm] using hzero

/-- Nonsingular integer exponent relations force all participating elements
of a commutative group to have finite order. -/
theorem finite_order_of_integer_relations {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [CommGroup G] (M : Matrix ι ι ℤ) (hdet : M.det ≠ 0)
    (x : ι → G) (h : ∀ i, ∏ j, x j ^ (M i j) = 1) (i : ι) :
    IsOfFinOrder (x i) := by
  have h' (k : ι) : ∑ j, M k j • Additive.ofMul (x j) = 0 := by
    simpa using congrArg Additive.ofMul (h k)
  have hz := det_zsmul_eq_zero_of_relations M (fun j => Additive.ofMul (x j)) h' i
  apply isOfFinOrder_iff_zpow_eq_one.mpr
  refine ⟨M.det, hdet, ?_⟩
  exact congrArg Additive.toMul hz

/-- The integer coefficient matrix of a Vafa-style weighted relation. -/
def vafaMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ι → ℕ) (b : ι → ℕ) :
    Matrix ι ι ℤ := fun i j => (if i = j then (b i : ℤ) else 0) - a i j

/-- A nonempty row of nonnegative weights yields strict diagonal dominance. -/
theorem vafaMatrix_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℕ) (b : ι → ℕ) (h : ∀ i, ∑ j, a i j < b i) :
    (vafaMatrix a b).det ≠ 0 := by
  classical
  let R : Matrix ι ι ℝ := (vafaMatrix a b).map (Int.castRingHom ℝ)
  have hr : R.det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have ht : ∑ j, (a i j : ℝ) < b i := by exact_mod_cast h i
    have hle : ∑ j ∈ Finset.univ.erase i, (a i j : ℝ) ≤ ∑ j, (a i j : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by simp)
    have ha : (a i i : ℝ) ≤ ∑ j, (a i j : ℝ) := by
      exact Finset.single_le_sum (fun j hj => Nat.cast_nonneg _) (Finset.mem_univ i)
    have hdiag : R i i = (b i : ℝ) - a i i := by
      simp [R, vafaMatrix]
    have hoff : ∀ j ∈ Finset.univ.erase i, ‖R i j‖ = (a i j : ℝ) := by
      intro j hj
      have hji : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      simp [R, vafaMatrix, hji, Real.norm_eq_abs]
    have hsum := Finset.sum_erase_add Finset.univ (fun j => (a i j : ℝ)) (Finset.mem_univ i)
    rw [Finset.sum_congr rfl hoff, hdiag, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  intro hz
  apply hr
  change ((vafaMatrix a b).map (Int.castRingHom ℝ)).det = 0
  have hh := Int.cast_det (R := ℝ) (vafaMatrix a b)
  rw [hz] at hh
  simpa using hh.symm

/-- The weighted Vafa relations imply every scalar is a root of unity. The
categorical proof of these relations is a separate obligation. -/
theorem finite_order_of_vafa_relations {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [CommGroup G] (a : ι → ι → ℕ) (b : ι → ℕ)
    (ha : ∀ i, ∑ j, a i j < b i) (x : ι → G)
    (h : ∀ i, x i ^ b i = ∏ j, x j ^ (a i j))
    (i : ι) : IsOfFinOrder (x i) := by
  apply finite_order_of_integer_relations (vafaMatrix a b) (vafaMatrix_det_ne_zero a b ha) x
  intro k
  have hs : (∏ j, x j ^ (if k = j then (b k : ℤ) else 0)) =
      x k ^ (b k : ℤ) := by
    simp [eq_comm]
  simp only [vafaMatrix, zpow_sub, div_eq_mul_inv, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, hs]
  have hh := h k
  have hh' : x k ^ (b k : ℤ) = ∏ j, x j ^ (a k j : ℤ) := by
    simpa only [zpow_natCast] using hh
  rw [hh', mul_inv_cancel]

end PropertyF.Ground.CentreCabling
