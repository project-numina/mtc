module
public import Mathlib.Tactic
public import Mathlib.Data.Matrix.Mul
open scoped BigOperators Matrix
@[expose] public noncomputable section
namespace PropertyF

/-- A positive matrix entry remains positive under further powers when every
diagonal entry is positive. -/
theorem matrix_pow_pos_mono {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (hA : ∀ i j, 0 ≤ A i j) (hdiag : ∀ i, 0 < A i i)
    (i j : ι) {m n : ℕ} (hmn : m ≤ n) (hm : 0 < (A ^ m) i j) : 0 < (A ^ n) i j := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ n h ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (Matrix.pow_apply_nonneg hA n i k) (hA k j)
    · exact ⟨j, Finset.mem_univ _, mul_pos ih (hdiag j)⟩

/-- For a finite nonnegative matrix with positive diagonal, reachability of
every pair implies that one power is strictly positive everywhere. -/
theorem matrix_exists_positive_power {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (hA : ∀ i j, 0 ≤ A i j) (hdiag : ∀ i, 0 < A i i)
    (hconnected : ∀ i j, ∃ n : ℕ, 0 < (A ^ n) i j) :
    ∃ n : ℕ, ∀ i j, 0 < (A ^ n) i j := by
  classical
  let k : ι × ι → ℕ := fun p => Classical.choose (hconnected p.1 p.2)
  let N := Finset.univ.sup k
  refine ⟨N, fun i j => ?_⟩
  apply matrix_pow_pos_mono A hA hdiag i j (Finset.le_sup (f := k) (Finset.mem_univ (i, j)))
  exact Classical.choose_spec (hconnected i j)
end PropertyF
