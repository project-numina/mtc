module
public import PropertyF.TraceBound
public import PropertyF.BraidAlgebra

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF

/-- The nonzero-weight argument in Lemma 3.2. An injective Galois map cannot
annihilate the original strictly positive sum of dimensions. -/
theorem MultiplicityData.weight_ne_zero {B : Blocks} (M : MultiplicityData B)
    (σ : ℂ ≃+* ℂ) (hpos : ∀ W, 0 < M.fpDimension W)
    (htransport : ∀ W, σ (M.fpDimension W : ℂ) = (M.dimension W : ℂ))
    (hretained : ∀ r, ∃ W, 0 < M.multiplicity W r) : ∀ r, M.weight r ≠ 0 := by
  intro r
  have hsum : 0 < ∑ W, (M.multiplicity W r : ℝ) * M.fpDimension W := by
    obtain ⟨W, hW⟩ := hretained r
    exact Finset.sum_pos' (fun W _ => mul_nonneg (Nat.cast_nonneg _) (hpos W).le)
      ⟨W, Finset.mem_univ _, mul_pos (by exact_mod_cast hW) (hpos W)⟩
  have hmap : σ (∑ W, (M.multiplicity W r : ℂ) * (M.fpDimension W : ℂ)) =
      (M.weight r : ℂ) := by
    simp [MultiplicityData.weight, map_sum, map_mul, htransport]
  intro hz
  have : (∑ W, (M.multiplicity W r : ℂ) * (M.fpDimension W : ℂ)) = 0 := by
    apply σ.injective
    simpa [hz] using hmap
  have hzero : (∑ W, (M.multiplicity W r : ℝ) * M.fpDimension W) = 0 := by
    exact_mod_cast this
  linarith

namespace ThreeStrandModel
variable {d f : ℝ} (M : ThreeStrandModel d f)

abbrev tr := M.overlap.tr 0

lemma simplePartial_cSquared (hd : d ≠ 0)
    (hS : M.pairTrace M.cSquared = (d : ℂ) * f) : M.simplePartial M.cSquared = f := by
  rw [M.pair_trace_partial] at hS
  exact mul_left_cancel₀ (by exact_mod_cast hd : (d : ℂ) ≠ 0) hS

/-- The exhibited braid attains the trace bound. Its trace is computed from the
two primitive partial traces, rather than included as an assumption. -/
lemma trace_aabb (hd : d ≠ 0) (hS : M.pairTrace M.cSquared = (d : ℂ) * f) :
    M.tr ((M.a ^ 2 * M.b ^ 2 : (M.overlap.stage 0).Algebraˣ) :
      (M.overlap.stage 0).Algebra) = (d : ℂ) * f ^ 2 := by
  calc
    _ = M.pairTrace (M.thirdPartial (M.leftPair M.cSquared * M.rightPair M.cSquared)) := by
      rw [M.left_cSquared, M.right_cSquared, M.trace_third]
      rfl
    _ = M.pairTrace ((f : ℂ) • (M.cSquared : M.pair.Algebra)) := by
      rw [M.third_bimodule, M.third_right, M.simplePartial_cSquared hd hS,
        mul_smul_comm, mul_one]
    _ = (d : ℂ) * f ^ 2 := by rw [map_smul, smul_eq_mul, hS]; ring

lemma aabb_unitary : (M.overlap.stage 0).IsUnitary
    ((M.a ^ 2 * M.b ^ 2 : (M.overlap.stage 0).Algebraˣ) : (M.overlap.stage 0).Algebra) := by
  simpa [pow_two] using Blocks.unitary_mul _
    (Blocks.unitary_mul _ M.a_unitary M.a_unitary)
    (Blocks.unitary_mul _ M.b_unitary M.b_unitary)

/-- The saturation argument and braid-algebra cancellation in Lemma 3.2. -/
lemma squares_equal (hd : d ≠ 0) (hf : 0 < f)
    (hw : ∀ r, (M.overlap.decomposition 0).weight r ≠ 0)
    (hS : M.pairTrace M.cSquared = (d : ℂ) * f) : M.a ^ 2 = M.b ^ 2 := by
  let B := M.overlap.stage 0
  let w := (M.overlap.decomposition 0).weight
  have hmass : B.mass w ≤ |d| * f ^ 2 := by
    have h := M.overlap.trace_bound hd hf (B.signElement_unitary w)
    change ‖B.trace w (B.signElement w)‖ ≤ _ at h
    rw [Blocks.trace_signElement] at h
    have hm0 : 0 ≤ B.mass w :=
      Finset.sum_nonneg (fun r _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0] using h
  have htrace : ‖M.tr ((M.a ^ 2 * M.b ^ 2 : B.Algebraˣ) : B.Algebra)‖ = |d| * f ^ 2 := by
    rw [M.trace_aabb hd hS]
    simp [norm_pow, abs_of_pos hf]
  have hsat : ‖M.tr ((M.a ^ 2 * M.b ^ 2 : B.Algebraˣ) : B.Algebra)‖ = B.mass w :=
    le_antisymm (B.norm_trace_le w M.aabb_unitary) (by rw [htrace]; exact hmass)
  have hc := B.central_of_saturation w hw M.aabb_unitary hsat
  apply squares_eq_of_central_product M.a M.b M.braid_relation
  apply Units.ext
  exact hc M.b

/-- Paper Lemma 3.2 from structural spherical calculus and the modular
self-braiding trace `hS`. No rigidity or centrality conclusion is an input. -/
theorem rigidity (hd : d ≠ 0) (hf : 0 < f)
    (hw : ∀ r, (M.overlap.decomposition 0).weight r ≠ 0)
    (hS : M.pairTrace M.cSquared = (d : ℂ) * f) : f = |d| := by
  have hab := M.squares_equal hd hf hw hS
  have heq : M.leftPair M.cSquared = M.rightPair M.cSquared := by
    rw [M.left_cSquared, M.right_cSquared, hab]
  have hpartial := congrArg M.thirdPartial heq
  rw [M.third_left, M.third_right, M.simplePartial_cSquared hd hS] at hpartial
  have hc : (M.cSquared : M.pair.Algebra) = (f / d : ℂ) • 1 := by
    apply (smul_right_injective _ (by exact_mod_cast hd : (d : ℂ) ≠ 0))
    change (d : ℂ) • (M.cSquared : M.pair.Algebra) = (d : ℂ) • ((f / d : ℂ) • 1)
    rw [hpartial, smul_smul]
    congr 1
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd]
  obtain ⟨n, hn, horder⟩ := M.finite_order
  apply fp_eq_abs_dim_of_finite_order hd hf
  refine ⟨n, hn, ?_⟩
  have hpow : ((f / d : ℂ) ^ n) • (1 : M.pair.Algebra) = 1 := by
    have h := congrArg (fun u : M.pair.Algebraˣ => (u : M.pair.Algebra)) horder
    simpa [hc, smul_pow] using h
  obtain ⟨r, hr⟩ := M.pair_nonzero
  let i : Fin (M.pair.size r) := ⟨0, hr⟩
  have hentry := congrArg (fun T : M.pair.Algebra => T r i i) hpow
  simpa using hentry

end ThreeStrandModel
end PropertyF
