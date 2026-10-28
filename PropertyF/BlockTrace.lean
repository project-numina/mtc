module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic

/-!
# Traces of unitary matrices and matrix blocks

Unitary matrix trace bounds, their equality case, and weighted traces on finite
products of matrix algebras.
-/

@[expose] public section
open scoped BigOperators ComplexConjugate
namespace PropertyF

/-- The column-norm consequence of a complex matrix being unitary. -/
def ColumnUnitary {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) : Prop :=
  ∀ j, ∑ i, Complex.normSq (U i j) = 1

variable {ι : Type*} [Fintype ι]

lemma columnUnitary_of_unitary [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : ColumnUnitary U := by
  intro j
  have h := congrArg (fun A : Matrix ι ι ℂ => (A j j).re)
    (Matrix.mem_unitaryGroup_iff'.mp hU)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re,
    Complex.normSq_apply, pow_two] using h

lemma entry_normSq_le_one {U : Matrix ι ι ℂ} (hU : ColumnUnitary U) (i j : ι) :
    Complex.normSq (U i j) ≤ 1 :=
  (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (U k j)) (Finset.mem_univ i)).trans_eq (hU j)

lemma entry_norm_le_one {U : Matrix ι ι ℂ} (hU : ColumnUnitary U) (i j : ι) :
    ‖U i j‖ ≤ 1 := by
  have h := entry_normSq_le_one hU i j
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (U i j)]

/-- The ordinary matrix trace estimate used twice in Section 3. -/
theorem norm_trace_le_card {U : Matrix ι ι ℂ} (hU : ColumnUnitary U) :
    ‖U.trace‖ ≤ Fintype.card ι := calc
    ‖U.trace‖ ≤ ∑ i, ‖U i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => entry_norm_le_one hU i i
    _ = Fintype.card ι := by simp

/-- Saturation of the real trace estimate forces the identity matrix. -/
theorem eq_one_of_re_trace_eq_card [DecidableEq ι] {U : Matrix ι ι ℂ} (hU : ColumnUnitary U)
    (ht : U.trace.re = Fintype.card ι) : U = 1 := by
  have hre : ∀ i, (U i i).re ≤ 1 := fun i =>
    (Complex.re_le_norm _).trans (entry_norm_le_one hU i i)
  have hsum : ∑ i, (U i i).re = ∑ _i : ι, (1 : ℝ) := by
    simpa [Matrix.trace, Matrix.diag] using ht
  have hdiagRe : ∀ i, (U i i).re = 1 := fun i =>
    (Finset.sum_eq_sum_iff_of_le (fun k _ => hre k)).mp hsum i (Finset.mem_univ i)
  have hdiag : ∀ i, U i i = 1 := by
    intro i
    have h := entry_normSq_le_one hU i i
    rw [Complex.normSq_apply, hdiagRe] at h
    have him : (U i i).im = 0 := by nlinarith [sq_nonneg (U i i).im]
    apply Complex.ext <;> simp [hdiagRe, him]
  ext i j
  by_cases hij : i = j
  · subst j; simp [hdiag]
  · have hsum' : ∑ k ∈ Finset.univ.erase j, Complex.normSq (U k j) = 0 := by
      have h := hU j
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hdiag] at h
      simpa using h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Complex.normSq_nonneg (U k j))).mp hsum' i (by simp [hij])
    simp [hij, Complex.normSq_eq_zero.mp hz]

/-- Equality in the complex trace bound forces a scalar matrix. This includes
zero-dimensional blocks and does not assume an eigenvalue decomposition. -/
theorem scalar_of_norm_trace_eq_card [DecidableEq ι] {U : Matrix ι ι ℂ} (hU : ColumnUnitary U)
    (ht : ‖U.trace‖ = Fintype.card ι) : ∃ z : ℂ, U = z • (1 : Matrix ι ι ℂ) := by
  by_cases hι : IsEmpty ι
  · let := hι
    exact ⟨1, Subsingleton.elim _ _⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have : Nonempty ι := not_isEmpty_iff.mp hι
    exact_mod_cast (Fintype.card_ne_zero (α := ι))
  let z : ℂ := U.trace / (Fintype.card ι : ℂ)
  have hz : ‖z‖ = 1 := by simp [z, ht, hn]
  have hzsq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hzmul : conj z * z = 1 := by
    rw [Complex.conj_mul', hz]; norm_num
  have hV : ColumnUnitary (conj z • U) := by
    intro j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_conj]
    rw [← Finset.mul_sum, hzsq, one_mul, hU j]
  have htr : (conj z • U).trace.re = Fintype.card ι := by
    have hc : U.trace = z * (Fintype.card ι : ℂ) := by
      dsimp [z]
      rw [div_mul_cancel₀ _ (by exact_mod_cast hn : (Fintype.card ι : ℂ) ≠ 0)]
    rw [Matrix.trace_smul, smul_eq_mul, hc, ← mul_assoc, hzmul, one_mul]
    simp
  have hVeq := eq_one_of_re_trace_eq_card hV htr
  refine ⟨z, ?_⟩
  have h := congrArg (fun V : Matrix ι ι ℂ => z • V) hVeq
  simpa [smul_smul, mul_comm z (conj z), hzmul] using h

end PropertyF

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF

/-- Explicit finite Wedderburn blocks, rather than an opaque trace space. -/
structure Blocks where
  /-- Number of matrix blocks. -/
  count : ℕ
  /-- Dimension of each block. -/
  size : Fin count → ℕ

namespace Blocks
/-- Product of the complex matrix algebras in the decomposition. -/
abbrev Algebra (B : Blocks) := ∀ r, Matrix (Fin (B.size r)) (Fin (B.size r)) ℂ

/-- Blockwise unitarity. -/
def IsUnitary (B : Blocks) (u : B.Algebra) : Prop :=
  ∀ r, u r ∈ Matrix.unitaryGroup (Fin (B.size r)) ℂ

/-- Weighted sum of the block traces. -/
def trace (B : Blocks) (w : Fin B.count → ℝ) (u : B.Algebra) : ℂ :=
  ∑ r, (w r : ℂ) * (u r).trace

/-- Weighted sum of the block dimensions. -/
def mass (B : Blocks) (w : Fin B.count → ℝ) : ℝ :=
  ∑ r, |w r| * B.size r

lemma norm_trace_le (B : Blocks) (w : Fin B.count → ℝ) {u : B.Algebra}
    (hu : B.IsUnitary u) : ‖B.trace w u‖ ≤ B.mass w := calc
    ‖B.trace w u‖ ≤ ∑ r, ‖(w r : ℂ) * (u r).trace‖ := norm_sum_le _ _
    _ = ∑ r, |w r| * ‖(u r).trace‖ := by simp
    _ ≤ B.mass w := Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left
        (by simpa using norm_trace_le_card (columnUnitary_of_unitary (hu r))) (abs_nonneg _)

/-- The sign element used on page 4, equation (3). -/
def signElement (B : Blocks) (w : Fin B.count → ℝ) : B.Algebra :=
  fun r => (if 0 ≤ w r then (1 : ℂ) else -1) • 1

lemma signElement_unitary (B : Blocks) (w : Fin B.count → ℝ) :
    B.IsUnitary (B.signElement w) := by
  intro r
  by_cases h : 0 ≤ w r <;>
    simp [signElement, h, Matrix.mem_unitaryGroup_iff]

lemma trace_signElement (B : Blocks) (w : Fin B.count → ℝ) :
    B.trace w (B.signElement w) = (B.mass w : ℂ) := by
  simp only [trace, mass, signElement, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : 0 ≤ w r
  · simp [h, abs_of_nonneg h]
  · simp [h, abs_of_neg (lt_of_not_ge h)]

/-- Equality in the weighted bound implies centrality when no weight vanishes.
This is the equality argument in Lemma 3.2, proved using actual complex matrices. -/
theorem central_of_saturation (B : Blocks) (w : Fin B.count → ℝ)
    (hw : ∀ r, w r ≠ 0) {g : B.Algebra} (hg : B.IsUnitary g)
    (hsat : ‖B.trace w g‖ = B.mass w) : ∀ T : B.Algebra, g * T = T * g := by
  have hle : ∀ r, |w r| * ‖(g r).trace‖ ≤ |w r| * B.size r := fun r =>
    mul_le_mul_of_nonneg_left
      (by simpa using norm_trace_le_card (columnUnitary_of_unitary (hg r))) (abs_nonneg _)
  have heq : ∑ r, |w r| * ‖(g r).trace‖ = ∑ r, |w r| * B.size r := by
    apply le_antisymm (Finset.sum_le_sum fun r _ => hle r)
    calc
      _ = ‖B.trace w g‖ := hsat.symm
      _ ≤ ∑ r, ‖(w r : ℂ) * (g r).trace‖ := norm_sum_le _ _
      _ = _ := by simp
  have hblock : ∀ r, ‖(g r).trace‖ = B.size r := by
    intro r
    have h := (Finset.sum_eq_sum_iff_of_le (fun r _ => hle r)).mp heq r (Finset.mem_univ r)
    exact (mul_left_cancel₀ (abs_ne_zero.mpr (hw r))) h
  intro T
  funext r
  obtain ⟨z, hz⟩ := scalar_of_norm_trace_eq_card (columnUnitary_of_unitary (hg r))
    (by simpa using hblock r)
  change g r * T r = T r * g r
  rw [hz, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end Blocks
end PropertyF
