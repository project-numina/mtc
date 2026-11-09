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
  norm_sum_le_of_le _ fun r _ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa using norm_trace_le_card (Pi.mem_unitary_iff.mp hu r)) (norm_nonneg _)

/-- A unitary block element aligning arbitrary complex weights. -/
def complexPhaseElement : B.Matrices := fun r => weightPhase (w r) • 1

lemma complexPhaseElement_unitary : B.IsUnitary (B.complexPhaseElement w) :=
  Pi.mem_unitary_iff.mpr fun r => by
    apply Unitary.smul_mem_of_mem ?_ (one_mem (unitary _))
    simp [Unitary.mem_iff, Complex.mul_conj', Complex.conj_mul',
      norm_weightPhase]

lemma complexTrace_phaseElement :
    B.complexTrace w (B.complexPhaseElement w) = (B.complexMass w : ℂ) := by
  simp [complexTrace, complexMass, complexPhaseElement, Matrix.trace_smul,
    ← mul_assoc, weight_mul_phase]

/-- A uniform unitary trace bound also bounds the full complex weight mass. -/
theorem complexMass_le_of_unitary_trace_bound {R : ℝ}
    (hbound : ∀ u, B.IsUnitary u → ‖B.complexTrace w u‖ ≤ R) :
    B.complexMass w ≤ R := by
  have hmass : 0 ≤ B.complexMass w :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  simpa [complexTrace_phaseElement, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmass]
    using hbound (B.complexPhaseElement w) (B.complexPhaseElement_unitary w)

/-- A unitary element attaining a uniform trace bound also saturates the
complex block mass. -/
theorem complexTrace_saturates_of_maximal_bound {R : ℝ} {u : B.Matrices}
    (hu : B.IsUnitary u) (hbound : ∀ v, B.IsUnitary v → ‖B.complexTrace w v‖ ≤ R)
    (hmax : ‖B.complexTrace w u‖ = R) :
    ‖B.complexTrace w u‖ = B.complexMass w :=
  le_antisymm (B.norm_complexTrace_le w hu) (by
    rw [hmax]
    exact B.complexMass_le_of_unitary_trace_bound w hbound)

/-- At equality, every nonzero-weight block has a saturated ordinary trace. -/
theorem complex_block_trace_norm_eq_of_saturation {u : B.Matrices}
    (hu : B.IsUnitary u) (hsat : ‖B.complexTrace w u‖ = B.complexMass w)
    (r : Fin B.count) (hw : w r ≠ 0) : ‖(u r).trace‖ = B.size r := by
  apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hw)
  simpa only [norm_mul] using
    norm_eq_of_sum_norm_eq (x := fun j => w j * (u j).trace)
      (b := fun j => ‖w j‖ * B.size j)
      (fun j => by
        simpa only [norm_mul] using mul_le_mul_of_nonneg_left
          (by simpa using norm_trace_le_card (Pi.mem_unitary_iff.mp hu j)) (norm_nonneg (w j)))
      hsat r

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

namespace MTC.Algebra

/-- A real-weighted sum inherits a common conjugate phase from every term
in the support of its weights. -/
theorem real_weighted_sum_phase {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (z : ι → ℂ) (ξ : ℂ)
    (hphase : ∀ i, r i ≠ 0 → z i = ξ * star (z i)) :
    (∑ i, (r i : ℂ) * z i) = ξ * star (∑ i, (r i : ℂ) * z i) := by
  change (∑ i, (r i : ℂ) * z i) =
    ξ * (starRingEnd ℂ) (∑ i, (r i : ℂ) * z i)
  simp only [map_sum, map_mul, starRingEnd_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r i = 0
  · simp [hi]
  · conv_lhs => rw [hphase i hi]
    simp [mul_left_comm]

/-- The scalar conclusion of the mixed-trace saturation argument. -/
theorem norm_eq_of_mixed_trace_saturation {t s d : ℂ} {f : ℝ}
    (hd : d ≠ 0) (hf : 0 ≤ f) (hmax : ‖t / d‖ = f)
    (hinv : ‖s‖ = ‖t‖) (hmixed : t * s / d = d ^ 3) : ‖d‖ = f := by
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hn := congrArg norm hmixed
  rw [norm_div, norm_mul, hinv, norm_pow] at hn
  rw [norm_div, div_eq_iff hdpos.ne'] at hmax
  rw [hmax, div_eq_iff hdpos.ne'] at hn
  have hsq : f ^ 2 = ‖d‖ ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hdpos.ne') (by nlinarith [hn])
  exact ((sq_eq_sq₀ hf hdpos.le).mp hsq).symm


end MTC.Algebra
