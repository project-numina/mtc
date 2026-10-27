module
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Pi

/-! Cyclic linear functionals on complex matrix algebras. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- A cyclic linear functional on a complex matrix algebra is a scalar
multiple of ordinary matrix trace, including the zero-dimensional case. -/
theorem cyclic_matrix_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ →ₗ[ℂ] ℂ) (hT : ∀ X Y, T (X * Y) = T (Y * X)) :
    ∃ w : ℂ, ∀ X, T X = w * X.trace := by
  classical
  by_cases hn : Nonempty ι
  · let i₀ : ι := Classical.choice hn
    let w := T (Matrix.single i₀ i₀ 1)
    refine ⟨w, fun X => ?_⟩
    have hs : ∀ i j (a : ℂ), T (Matrix.single i j a) =
        w * (Matrix.single i j a).trace := by
      intro i j a
      by_cases hij : i = j
      · subst j
        have hdiag := hT (Matrix.single i i₀ a) (Matrix.single i₀ i (1 : ℂ))
        simp only [Matrix.single_mul_single_same, mul_one, one_mul] at hdiag
        have hscalar : Matrix.single i₀ i₀ a = a • Matrix.single i₀ i₀ (1 : ℂ) := by
          simp [Matrix.smul_single]
        rw [hdiag, hscalar, map_smul, Matrix.trace_single_eq_same]
        simp [w, mul_comm]
      · have hoff := hT (Matrix.single i i (1 : ℂ)) (Matrix.single i j a)
        have hz : Matrix.single i j a * Matrix.single i i (1 : ℂ) = 0 :=
          Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) 1
        simp only [Matrix.single_mul_single_same, one_mul, hz, map_zero] at hoff
        rw [hoff, Matrix.trace_single_eq_of_ne _ _ _ hij, mul_zero]
    calc
      T X = ∑ i, ∑ j, T (Matrix.single i j (X i j)) := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single X]
        simp only [map_sum]
      _ = ∑ i, ∑ j, w * (Matrix.single i j (X i j)).trace := by simp only [hs]
      _ = w * X.trace := by
        simp_rw [← Finset.mul_sum]
        congr 1
        conv_rhs => rw [Matrix.matrix_eq_sum_single X]
        simp only [Matrix.trace_sum]
  · have hempty : IsEmpty ι := not_nonempty_iff.mp hn
    let _ := hempty
    refine ⟨0, fun X => ?_⟩
    have hX : X = 0 := Subsingleton.elim _ _
    simp [hX]

/-- Every cyclic linear functional on a finite product of matrix algebras is
a weighted sum of ordinary block traces. The weights may be arbitrary complex
numbers; reality and categorical multiplicities require additional input. -/
theorem cyclic_block_trace {n : ℕ} (d : Fin n → ℕ)
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ X Y, T (X * Y) = T (Y * X)) :
    ∃ w : Fin n → ℂ, ∀ X, T X = ∑ i, w i * (X i).trace := by
  classical
  let V : Fin n → Type := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ
  let Tblock (i : Fin n) : V i →ₗ[ℂ] ℂ := T.comp (LinearMap.single ℂ V i)
  have hmul (i : Fin n) (X Y : V i) :
      Pi.single i (X * Y) = (Pi.single i X : ∀ i, V i) * Pi.single i Y := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  have hc (i : Fin n) : ∀ X Y : V i, Tblock i (X * Y) = Tblock i (Y * X) := by
    intro X Y
    change T (Pi.single i (X * Y)) = T (Pi.single i (Y * X))
    rw [hmul, hmul]
    exact hT _ _
  have hw : ∀ i, ∃ w : ℂ, ∀ X : V i, Tblock i X = w * X.trace :=
    fun i => cyclic_matrix_trace (Tblock i) (hc i)
  choose w hw using hw
  refine ⟨w, fun X => ?_⟩
  calc
    T X = ∑ i, Tblock i (X i) := by
      conv_lhs => rw [← LinearMap.sum_single_apply V X]
      simp [Tblock]
    _ = ∑ i, w i * (X i).trace := by simp [hw]

end PropertyF.Ground.Calculus
