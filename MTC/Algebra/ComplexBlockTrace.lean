module
public import MTC.Algebra.BlockTrace
public import MTC.Braided.BraidAlgebra

/-!
# Complex weighted block traces

Equality in a trace bound only forces scalarity in blocks on which the
complex weight is nonzero. The weights may have arbitrary phases or vanish.
-/

open scoped BigOperators ComplexConjugate

@[expose] public noncomputable section
namespace MTC.Algebra.Blocks

variable (B : Blocks) (w : Fin B.count → ℂ)

/-- A weighted matrix trace with complex weights. -/
def complexTrace (u : B.Matrices) : ℂ := ∑ r, w r * (u r).trace

/-- The total absolute weight, including the matrix dimensions. -/
def complexMass : ℝ := ∑ r, ‖w r‖ * B.size r

/-- The norm of a weighted unitary trace is bounded by its total mass. -/
theorem norm_complexTrace_le {u : B.Matrices} (hu : B.IsUnitary u) :
    ‖B.complexTrace w u‖ ≤ B.complexMass w :=
  (norm_sum_le _ _).trans <| Finset.sum_le_sum fun r _ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa using norm_trace_le_card (Pi.mem_unitary_iff.mp hu r)) (norm_nonneg _)

/-- A unitary scalar whose product with a weight is its absolute value. -/
def weightPhase (z : ℂ) : ℂ := if z = 0 then 1 else star z / ‖z‖

lemma norm_weightPhase (z : ℂ) : ‖weightPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [weightPhase, hz]
  · simp [weightPhase, hz, norm_ne_zero_iff.mpr hz]

lemma weight_mul_phase (z : ℂ) : z * weightPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [weightPhase, hz]
  · simp [weightPhase, hz, ← mul_div_assoc, Complex.mul_conj',
      pow_two, Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)]

/-- A unitary block element aligning arbitrary complex weights. -/
def complexPhaseElement : B.Matrices := fun r => weightPhase (w r) • 1

lemma complexPhaseElement_unitary : B.IsUnitary (B.complexPhaseElement w) :=
  Pi.mem_unitary_iff.mpr fun r => by
    apply Unitary.smul_mem_of_mem ?_ (one_mem (unitary _))
    simp [Unitary.mem_iff, Complex.mul_conj', Complex.conj_mul',
      norm_weightPhase]

lemma complexTrace_phaseElement :
    B.complexTrace w (B.complexPhaseElement w) = (B.complexMass w : ℂ) := by
  rw [complexTrace, complexMass, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp [complexPhaseElement, Matrix.trace_smul, ← mul_assoc, weight_mul_phase]

/-- A uniform unitary trace bound also bounds the full complex weight mass. -/
theorem complexMass_le_of_unitary_trace_bound {R : ℝ}
    (hbound : ∀ u, B.IsUnitary u → ‖B.complexTrace w u‖ ≤ R) :
    B.complexMass w ≤ R := by
  have hmass : 0 ≤ B.complexMass w :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  simpa [complexTrace_phaseElement, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmass]
    using hbound (B.complexPhaseElement w) (B.complexPhaseElement_unitary w)

/-- At equality, every nonzero-weight block has a saturated ordinary trace. -/
theorem complex_block_trace_norm_eq_of_saturation {u : B.Matrices}
    (hu : B.IsUnitary u) (hsat : ‖B.complexTrace w u‖ = B.complexMass w)
    (r : Fin B.count) (hw : w r ≠ 0) : ‖(u r).trace‖ = B.size r := by
  have hle : ∀ j, ‖w j‖ * ‖(u j).trace‖ ≤ ‖w j‖ * B.size j := fun j =>
    mul_le_mul_of_nonneg_left
      (by simpa using norm_trace_le_card (Pi.mem_unitary_iff.mp hu j)) (norm_nonneg _)
  have heq : ∑ j, ‖w j‖ * ‖(u j).trace‖ = ∑ j, ‖w j‖ * B.size j :=
    le_antisymm (Finset.sum_le_sum fun j _ => hle j) (calc
      _ = ‖B.complexTrace w u‖ := hsat.symm
      _ ≤ ∑ j, ‖w j * (u j).trace‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul])
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hw)
    ((Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp heq r (Finset.mem_univ r))

/-- A saturated unitary block commutes with every matrix on the support of
its complex weight. -/
theorem complex_block_central_of_saturation {u : B.Matrices}
    (hu : B.IsUnitary u) (hsat : ‖B.complexTrace w u‖ = B.complexMass w)
    (r : Fin B.count) (hw : w r ≠ 0) (T : B.Matrices) :
    u r * T r = T r * u r := by
  obtain ⟨z, hz⟩ := scalar_of_norm_trace_eq_card (Pi.mem_unitary_iff.mp hu r)
    (by simpa using B.complex_block_trace_norm_eq_of_saturation w hu hsat r hw)
  simp [hz]

/-- If all weights share a conjugate phase, the weighted trace of the
adjoint has the same phase times the conjugate original trace. -/
theorem complexTrace_star_of_weight_phase (B : Blocks) (w : Fin B.count → ℂ)
    (ξ : ℂ) (hphase : ∀ r, w r = ξ * star (w r)) (u : B.Matrices) :
    B.complexTrace w (star u) = ξ * star (B.complexTrace w u) := by
  simp only [complexTrace, Pi.star_apply, Matrix.star_eq_conjTranspose,
    Matrix.trace_conjTranspose]
  change (∑ r, w r * star (u r).trace) =
    ξ * (starRingEnd ℂ) (∑ r, w r * (u r).trace)
  simp only [map_sum, map_mul, starRingEnd_apply, Finset.mul_sum, ← mul_assoc, ← hphase]

/-- A unit-modulus common weight phase gives equal trace norms for a unitary
and its adjoint, with no nonzero-weight assumption. -/
theorem norm_complexTrace_star_of_weight_phase (B : Blocks) (w : Fin B.count → ℂ)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (hphase : ∀ r, w r = ξ * star (w r))
    (u : B.Matrices) : ‖B.complexTrace w (star u)‖ = ‖B.complexTrace w u‖ := by
  rw [complexTrace_star_of_weight_phase B w ξ hphase, norm_mul, hξ, norm_star, one_mul]


end MTC.Algebra.Blocks
