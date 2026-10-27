module
public import PropertyF.Ground.Cabling.Perron
public import PropertyF.Ground.Cabling.Primitive
open scoped Matrix BigOperators
@[expose] public noncomputable section
namespace PropertyF

/-- Powers of a matrix act on an eigenvector by powers of its eigenvalue. -/
theorem matrix_pow_mulVec_eigen {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (d : ℝ) (h : A *ᵥ v = d • v) :
    ∀ n : ℕ, A ^ n *ᵥ v = (d ^ n) • v
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ', ← Matrix.mulVec_mulVec, matrix_pow_mulVec_eigen A v d h n,
        Matrix.mulVec_smul, h, smul_smul]
      simp [pow_succ, mul_comm]

/-- A nonnegative rational matrix with positive diagonal and strongly
connected powers has integer coordinates on its normalized positive integral
eigenvector, whenever the eigenvalue is rational. This packages the matrix
and arithmetic parts of the ENO 8.27 argument. -/
theorem connectedMatrix_eigenvector_integral {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (a : Matrix ι ι ℚ) (v : ι → ℝ) (eig : ℚ) (o : ι)
    (ha : ∀ i j, 0 ≤ a i j) (hdiag : ∀ i, 0 < a i i)
    (hconnected : ∀ i j, ∃ n : ℕ, 0 < (a ^ n) i j)
    (hv : ∀ i, 0 < v i)
    (hve : ∀ i, ∑ j, (a i j : ℝ) * v j = (eig : ℝ) * v i)
    (hv0 : v o = 1) (hIntegral : ∀ i, IsIntegral ℤ (v i)) :
    ∀ i, ∃ z : ℤ, v i = z := by
  classical
  obtain ⟨n, hn⟩ := matrix_exists_positive_power a ha hdiag hconnected
  let A : Matrix ι ι ℝ := a.map (Rat.castHom ℝ)
  have h : A *ᵥ v = (eig : ℝ) • v := by
    ext i
    simpa [A, Matrix.mulVec, dotProduct] using hve i
  have hp := matrix_pow_mulVec_eigen A v (eig : ℝ) h n
  have hpn : ∀ i, ∑ j, ((a ^ n) i j : ℝ) * v j = ((eig ^ n : ℚ) : ℝ) * v i := by
    intro i
    have hpi := congrFun hp i
    have hmap : A ^ n = (a ^ n).map (Rat.castHom ℝ) := by
      change (Rat.castHom ℝ).mapMatrix a ^ n = (Rat.castHom ℝ).mapMatrix (a ^ n)
      exact (map_pow (Rat.castHom ℝ).mapMatrix a n).symm
    rw [hmap] at hpi
    simpa [Matrix.mulVec, dotProduct] using hpi
  exact positiveMatrix_eigenvector_integral (a ^ n) v (eig ^ n) o hn hv hpn hv0 hIntegral
end PropertyF
