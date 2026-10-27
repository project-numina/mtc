module
public import PropertyF.Ground.Fusion.PositiveMatrix
public import Mathlib.Analysis.Matrix.Spectrum

/-! Perron theory for positive symmetric real matrices. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open WithLp

namespace PropertyF.Ground

def euclideanAbs {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => |x i|)

theorem euclideanAbs_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖euclideanAbs x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, euclideanAbs]

/-- Replacing coordinates by absolute values cannot decrease the quadratic
form of a matrix with nonnegative entries. -/
theorem quadratic_le_abs {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (x : ι → ℝ) :
    ∑ i, ∑ j, x i * A i j * x j ≤
      ∑ i, ∑ j, |x i| * A i j * |x j| := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (le_abs_self (x i * x j)) (hA i j)
  simpa [abs_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem matrix_quadratic_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x =
      ∑ i, ∑ j, x i * A i j * x j := by
  simp [ContinuousLinearMap.reApplyInnerSelf, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc,
    mul_comm, mul_left_comm]

/-- A strictly positive symmetric real matrix has a strictly positive
eigenvector. -/
theorem positive_symmetric_matrix_has_positive_eigenvector {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ)
    (hsym : A.IsHermitian) (hpos : ∀ i j, 0 < A i j) :
    ∃ (d : ℝ) (v : ι → ℝ), (∀ i, 0 < v i) ∧ A *ᵥ v = d • v := by
  classical
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hself : IsSelfAdjoint T := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hsym
  obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ ι, z ≠ 0 := exists_ne 0
  have hcompact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ ι) ‖z‖) :=
    isCompact_sphere _ _
  obtain ⟨x, hxmem, hxmax⟩ := hcompact.exists_isMaxOn ⟨z, by simp⟩
    T.reApplyInnerSelf_continuous.continuousOn
  let y := euclideanAbs x
  have hynorm : ‖y‖ = ‖z‖ := by
    rw [euclideanAbs_norm]
    simpa using hxmem
  have hyne : y ≠ 0 := by
    intro h
    have := hynorm
    rw [h] at this
    simp only [norm_zero] at this
    exact hz (norm_eq_zero.mp this.symm)
  have hynonneg (i : ι) : 0 ≤ y i := abs_nonneg _
  have hyexists : ∃ i, 0 < y i := by
    by_contra h
    push Not at h
    apply hyne
    ext i
    have := hynonneg i
    have := h i
    simp only [PiLp.zero_apply]
    linarith
  have hyquad : T.reApplyInnerSelf x ≤ T.reApplyInnerSelf y := by
    change (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x ≤
      (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf y
    rw [matrix_quadratic_form, matrix_quadratic_form]
    simpa [y, euclideanAbs] using quadratic_le_abs A (fun i j => (hpos i j).le) (fun i => x i)
  have hymax : IsMaxOn T.reApplyInnerSelf (Metric.sphere 0 ‖y‖) y := by
    intro w hw
    have hw' : w ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) ‖z‖ := by simpa [hynorm] using hw
    exact (hxmax hw').trans hyquad
  have heigen := hself.eq_smul_self_of_isLocalExtrOn (Or.inr hymax.isLocalMaxOn)
  let d := T.rayleighQuotient y
  have heigen' : A *ᵥ (fun i => y i) = d • (fun i => y i) := by
    have h := congrArg ofLp heigen
    simpa [T, d, Matrix.toLpLin_apply] using h
  obtain ⟨j, hj⟩ := hyexists
  have hypos (i : ι) : 0 < y i := by
    have hsum : 0 < ∑ k, A i k * y k :=
      Finset.sum_pos' (fun k _ => mul_nonneg (hpos i k).le (hynonneg k))
        ⟨j, Finset.mem_univ _, mul_pos (hpos i j) hj⟩
    have hi := congrFun heigen' i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    have : 0 < d * y i := by linarith
    by_contra hn
    have : y i = 0 := le_antisymm (le_of_not_gt hn) (hynonneg i)
    simp [this] at *
  exact ⟨d, fun i => y i, hypos, heigen'⟩

end PropertyF.Ground
