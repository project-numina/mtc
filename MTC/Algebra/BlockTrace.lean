module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Tactic

/-!
# Traces of unitary matrices and matrix blocks

Unitary matrix trace bounds, their equality case, and weighted traces on finite
products of matrix algebras.
-/

@[expose] public section
open scoped BigOperators ComplexConjugate ComplexOrder Matrix
namespace MTC.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Blocks

/-- A unitary scalar whose product with a weight is its absolute value. -/
noncomputable def weightPhase (z : ℂ) : ℂ := if z = 0 then 1 else star z / ‖z‖

lemma norm_weightPhase (z : ℂ) : ‖weightPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [weightPhase, hz]
  · simp [weightPhase, hz, norm_ne_zero_iff.mpr hz]

lemma weight_mul_phase (z : ℂ) : z * weightPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [weightPhase, hz]
  · simp [weightPhase, hz, ← mul_div_assoc, Complex.mul_conj',
      pow_two, Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)]

end Blocks

section UnitaryTrace

variable {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ)
include hU

/-- The ordinary matrix trace estimate used twice in Section 3. -/
theorem norm_trace_le_card :
    ‖U.trace‖ ≤ Fintype.card ι := by
  simpa [Matrix.trace] using
    norm_sum_le_of_le Finset.univ (fun i _ => entry_norm_bound_of_unitary hU i i)

/-- Saturation of the real trace estimate forces the identity matrix. -/
theorem eq_one_of_re_trace_eq_card (ht : U.trace.re = Fintype.card ι) : U = 1 :=
  sub_eq_zero.mp <| Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp <| by
    simp [Complex.ext_iff, Matrix.conjTranspose_sub, sub_mul, mul_sub, Matrix.trace_sub,
      Matrix.trace_conjTranspose, ht, show Uᴴ * U = 1 from Matrix.mem_unitaryGroup_iff'.mp hU]

/-- Equality in the complex trace bound forces a scalar matrix. This includes
zero-dimensional blocks and does not assume an eigenvalue decomposition. -/
theorem scalar_of_norm_trace_eq_card (ht : ‖U.trace‖ = Fintype.card ι) :
    ∃ z : ℂ, U = z • (1 : Matrix ι ι ℂ) := by
  let z := Blocks.weightPhase U.trace
  have hz : ‖z‖ = 1 := Blocks.norm_weightPhase _
  have hzmul : conj z * z = 1 := by simp [Complex.conj_mul', hz]
  have hV : z • U ∈ Matrix.unitaryGroup ι ℂ :=
    Unitary.smul_mem_of_mem (by simpa [Unitary.mem_iff, mul_comm] using hzmul) hU
  have htr : (z • U).trace.re = Fintype.card ι := by
    simp only [Matrix.trace_smul, smul_eq_mul]
    rw [mul_comm, show U.trace * z = (‖U.trace‖ : ℂ) from Blocks.weight_mul_phase _]
    simpa using ht
  refine ⟨conj z, ?_⟩
  simpa [smul_smul, hzmul] using
    congrArg (fun V : Matrix ι ι ℂ => conj z • V) (eq_one_of_re_trace_eq_card hV htr)

end UnitaryTrace

end MTC.Algebra

@[expose] public noncomputable section
open scoped BigOperators
namespace MTC.Algebra

/-- If a finite sum attains a sum of termwise norm bounds, each term
attains its bound. No positivity or nonvanishing of the individual terms is
required. -/
theorem norm_eq_of_sum_norm_eq {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    {x : ι → E} {b : ι → ℝ}
    (hbound : ∀ i, ‖x i‖ ≤ b i) (hsat : ‖∑ i, x i‖ = ∑ i, b i) (i : ι) :
    ‖x i‖ = b i := by
  have heq : ∑ i, ‖x i‖ = ∑ i, b i :=
    le_antisymm (Finset.sum_le_sum fun i _ => hbound i)
      (hsat.symm.le.trans (norm_sum_le _ _))
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hbound i)).mp heq i (Finset.mem_univ i)

/-- Explicit finite Wedderburn blocks, rather than an opaque trace space. -/
structure Blocks where
  /-- Number of matrix blocks. -/
  count : ℕ
  /-- Dimension of each block. -/
  size : Fin count → ℕ

namespace Blocks
/-- Product of the complex matrix algebras in the decomposition. -/
abbrev Matrices (B : Blocks) := ∀ r, Matrix (Fin (B.size r)) (Fin (B.size r)) ℂ

/-- Unitarity in the product of matrix blocks. -/
abbrev IsUnitary (B : Blocks) (u : B.Matrices) : Prop := u ∈ unitary B.Matrices

/-- Weighted sum of the block traces. -/
def trace (B : Blocks) (w : Fin B.count → ℝ) (u : B.Matrices) : ℂ :=
  ∑ r, (w r : ℂ) * (u r).trace

/-- Weighted sum of the block dimensions. -/
def mass (B : Blocks) (w : Fin B.count → ℝ) : ℝ :=
  ∑ r, |w r| * B.size r

variable (B : Blocks) (w : Fin B.count → ℝ)

/-- Weighted block mass is nonnegative. -/
lemma mass_nonneg : 0 ≤ B.mass w :=
  Finset.sum_nonneg fun _r _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

/-- The norm of a unitary weighted trace is bounded by the block mass. -/
lemma norm_trace_le {u : B.Matrices}
    (hu : B.IsUnitary u) : ‖B.trace w u‖ ≤ B.mass w :=
  norm_sum_le_of_le _ fun r _ => by
    simpa using mul_le_mul_of_nonneg_left
      (by simpa using norm_trace_le_card (Pi.mem_unitary_iff.mp hu r)) (abs_nonneg (w r))

/-- The sign element used on page 4, equation (3). -/
def signElement : B.Matrices :=
  fun r => (if 0 ≤ w r then (1 : ℂ) else -1) • 1

/-- The sign element is unitary in every block. -/
lemma signElement_unitary :
    B.IsUnitary (B.signElement w) := Pi.mem_unitary_iff.mpr fun r => by
  by_cases h : 0 ≤ w r <;> simp [signElement, h, Matrix.mem_unitaryGroup_iff]

/-- The sign element attains the total weighted block mass. -/
lemma trace_signElement :
    B.trace w (B.signElement w) = (B.mass w : ℂ) :=
  (Finset.sum_congr rfl fun r _ => by
    by_cases h : 0 ≤ w r <;> simp [signElement, h, abs_of_nonneg, abs_of_neg, lt_of_not_ge]).trans
      (Complex.ofReal_sum _ _).symm

/-- A bound on all unitary traces bounds the total weighted block mass. -/
lemma mass_le_of_unitary_trace_bound {R : ℝ}
    (hbound : ∀ u, B.IsUnitary u → ‖B.trace w u‖ ≤ R) : B.mass w ≤ R := by
  simpa [B.trace_signElement, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (B.mass_nonneg w)] using hbound (B.signElement w) (B.signElement_unitary w)

section Saturation

variable {g : B.Matrices} (hg : B.IsUnitary g) (hsat : ‖B.trace w g‖ = B.mass w)
include hg hsat

/-- Saturation of the weighted bound saturates every block with nonzero weight. -/
theorem block_trace_norm_eq_of_saturation (r : Fin B.count) (hw : w r ≠ 0) : ‖(g r).trace‖ = B.size r := by
  apply mul_left_cancel₀ (abs_ne_zero.mpr hw)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    norm_eq_of_sum_norm_eq (x := fun j => (w j : ℂ) * (g j).trace)
      (b := fun j => |w j| * B.size j)
      (fun j => by
        simpa using mul_le_mul_of_nonneg_left
          (by simpa using norm_trace_le_card (Pi.mem_unitary_iff.mp hg j)) (abs_nonneg (w j)))
      hsat r

/-- Equality in the weighted bound implies centrality when no weight vanishes.
This is the equality argument in Lemma 3.2, proved using actual complex matrices. -/
theorem central_of_saturation (hw : ∀ r, w r ≠ 0) : ∀ T : B.Matrices, g * T = T * g :=
  fun T => funext fun r => (scalar_of_norm_trace_eq_card (Pi.mem_unitary_iff.mp hg r)
    (by simpa using B.block_trace_norm_eq_of_saturation w hg hsat r (hw r))).elim fun _ hz =>
      by simp [hz]

end Saturation

end Blocks
end MTC.Algebra
