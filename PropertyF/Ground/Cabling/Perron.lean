module
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Algebra.BigOperators.Ring.Finset
open scoped BigOperators Matrix
@[expose] public noncomputable section
namespace PropertyF

/-- A strictly positive finite matrix has at most one eigenvector with a given
normalization, provided it has a strictly positive eigenvector. -/
theorem positiveMatrix_eigenvector_unique {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → ι → ℝ) (v w : ι → ℝ) (eig : ℝ)
    (ha : ∀ i j, 0 < a i j) (hv : ∀ i, 0 < v i)
    (hve : ∀ i, ∑ j, a i j * v j = eig * v i)
    (hwe : ∀ i, ∑ j, a i j * w j = eig * w i) :
    ∃ t : ℝ, ∀ i, w i = t * v i := by
  classical
  obtain ⟨m, hm⟩ := Finset.exists_min_image Finset.univ (fun i => w i / v i) Finset.univ_nonempty
  let t := w m / v m
  have hz : ∀ i, 0 ≤ w i - t * v i := by
    intro i
    have hmi : t ≤ w i / v i := hm.2 i (Finset.mem_univ i)
    exact sub_nonneg.mpr ((le_div_iff₀ (hv i)).mp hmi)
  have hzm : w m - t * v m = 0 := by
    simp [t, ne_of_gt (hv m)]
  have heq : ∑ j, a m j * (w j - t * v j) = 0 := by
    simp_rw [mul_sub, show ∀ j, a m j * (t * v j) = t * (a m j * v j) by intro; ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hwe, hve]
    rw [sub_eq_zero.mp hzm]; ring
  refine ⟨t, fun i => ?_⟩
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (le_of_lt (ha m j)) (hz j))).mp heq i (Finset.mem_univ i)
  have : w i - t * v i = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt (ha m i))
  exact sub_eq_zero.mp this
/-- A normalized rational eigenvector identifies every coordinate of a
normalized positive eigenvector. -/
theorem positiveMatrix_eigenvector_rational {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → ι → ℚ) (v : ι → ℝ) (q : ι → ℚ) (eig : ℚ) (o : ι)
    (ha : ∀ i j, 0 < a i j) (hv : ∀ i, 0 < v i)
    (hve : ∀ i, ∑ j, (a i j : ℝ) * v j = (eig : ℝ) * v i)
    (hqe : ∀ i, ∑ j, a i j * q j = eig * q i)
    (hv0 : v o = 1) (hq0 : q o = 1) : ∀ i, v i = (q i : ℝ) := by
  have hq : ∀ i, ∑ j, (a i j : ℝ) * (q j : ℝ) = (eig : ℝ) * (q i : ℝ) := by
    intro i
    exact_mod_cast hqe i
  obtain ⟨t, ht⟩ := positiveMatrix_eigenvector_unique
    (fun i j => (a i j : ℝ)) v (fun i => (q i : ℝ)) (eig : ℝ)
    (fun i j => by exact_mod_cast ha i j) hv hve hq
  have hto := ht o
  rw [hq0, Rat.cast_one, hv0, mul_one] at hto
  have : t = 1 := hto.symm
  intro i
  simpa [this] using (ht i).symm
/-- A strictly positive rational matrix with a rational eigenvalue has a
rational normalized positive eigenvector. -/
theorem positiveMatrix_eigenvector_rat {ι : Type} [Fintype ι] [Nonempty ι]
    (a : Matrix ι ι ℚ) (v : ι → ℝ) (eig : ℚ) (o : ι)
    (ha : ∀ i j, 0 < a i j) (hv : ∀ i, 0 < v i)
    (hve : ∀ i, ∑ j, (a i j : ℝ) * v j = (eig : ℝ) * v i)
    (hv0 : v o = 1) : ∀ i, ∃ q : ℚ, v i = q := by
  classical
  let M : Matrix ι ι ℚ := a - eig • 1
  let MR : Matrix ι ι ℝ := M.map (Rat.castHom ℝ)
  have hvne : v ≠ 0 := by
    intro h
    have := congrFun h o
    simp [hv0] at this
  have hvker : MR *ᵥ v = 0 := by
    ext i
    change (∑ j, (((a i j - eig * (1 : Matrix ι ι ℚ) i j : ℚ) : ℝ) * v j)) = 0
    simp only [Rat.cast_sub, Rat.cast_mul, sub_mul, Finset.sum_sub_distrib, hve]
    simp [Matrix.one_apply, apply_ite, ite_mul]
  have hdR : MR.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hvker⟩
  have hdQ : M.det = 0 := by
    have hh : ((M.det : ℚ) : ℝ) = 0 := by
      have hmap := (Rat.castHom ℝ).map_det M
      change (M.det : ℝ) = (M.map (Rat.castHom ℝ)).det at hmap
      rw [hmap]
      exact hdR
    exact_mod_cast hh
  obtain ⟨q, hqne, hqker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdQ
  have hqe : ∀ i, ∑ j, a i j * q j = eig * q i := by
    intro i
    have h := congrFun hqker i
    simp [M, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply] at h
    exact sub_eq_zero.mp h
  have hq : ∀ i, ∑ j, (a i j : ℝ) * (q j : ℝ) = (eig : ℝ) * (q i : ℝ) := by
    intro i
    exact_mod_cast hqe i
  obtain ⟨t, ht⟩ := positiveMatrix_eigenvector_unique
    (fun i j => (a i j : ℝ)) v (fun i => (q i : ℝ)) (eig : ℝ)
    (fun i j => by exact_mod_cast ha i j) hv hve hq
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hqne
    funext i
    apply Rat.cast_injective (α := ℝ)
    simpa [ht0] using ht i
  have ho : (q o : ℝ) = t := by simpa [hv0] using ht o
  intro i
  refine ⟨q i / q o, ?_⟩
  rw [Rat.cast_div, ht i, ho]
  field_simp
/-- The normalized positive eigenvector has integer coordinates whenever its
coordinates are algebraic integers. This is the arithmetic step in ENO 8.27. -/
theorem positiveMatrix_eigenvector_integral {ι : Type} [Fintype ι] [Nonempty ι]
    (a : Matrix ι ι ℚ) (v : ι → ℝ) (eig : ℚ) (o : ι)
    (ha : ∀ i j, 0 < a i j) (hv : ∀ i, 0 < v i)
    (hve : ∀ i, ∑ j, (a i j : ℝ) * v j = (eig : ℝ) * v i)
    (hv0 : v o = 1) (hIntegral : ∀ i, IsIntegral ℤ (v i)) :
    ∀ i, ∃ z : ℤ, v i = z := by
  intro i
  obtain ⟨q, hq⟩ := positiveMatrix_eigenvector_rat a v eig o ha hv hve hv0 i
  have hr : v i ∈ Set.range (Rat.cast : ℚ → ℝ) := ⟨q, hq.symm⟩
  obtain ⟨z, hz⟩ := (hIntegral i).mem_range_ratCast_iff.mp hr
  exact ⟨z, hz.symm⟩
end PropertyF
