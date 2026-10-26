module
public import PropertyF.Axioms
public import PropertyF.PowerBound

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF

lemma MultiplicityData.mass_le_fpMass {B : Blocks} (M : MultiplicityData B) :
    B.mass M.weight ≤ M.fpMass := by
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    |∑ W, (M.multiplicity W r : ℝ) * M.dimension W| ≤
        ∑ W, |(M.multiplicity W r : ℝ) * M.dimension W| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ W, (M.multiplicity W r : ℝ) * |M.dimension W| := by
      simp [abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (M.multiplicity _ r : ℝ) ≥ 0)]
    _ ≤ ∑ W, (M.multiplicity W r : ℝ) * M.fpDimension W := by
      apply Finset.sum_le_sum
      intro W _
      exact mul_le_mul_of_nonneg_left (M.dimension_bound W) (Nat.cast_nonneg _)

lemma Blocks.unitary_mul (B : Blocks) {u v : B.Algebra}
    (hu : B.IsUnitary u) (hv : B.IsUnitary v) : B.IsUnitary (u * v) := by
  intro r
  exact (Matrix.unitaryGroup (Fin (B.size r)) ℂ).mul_mem (hu r) (hv r)

lemma Blocks.unitary_map {B C : Blocks} (F : B.Algebra →⋆ₐ[ℂ] C.Algebra)
    {u : B.Algebra} (hu : B.IsUnitary u) : C.IsUnitary (F u) := by
  have hl : star u * u = 1 := by
    funext r
    exact Matrix.mem_unitaryGroup_iff'.mp (hu r)
  have hr : u * star u = 1 := by
    funext r
    exact Matrix.mem_unitaryGroup_iff.mp (hu r)
  intro r
  apply Matrix.mem_unitaryGroup_iff.mpr
  have h := congrArg (fun v : C.Algebra => v r) (congrArg F hr)
  simpa only [map_mul, map_star, map_one, Pi.mul_apply, Pi.star_apply, Pi.one_apply] using h

namespace OverlapModel
variable {d f : ℝ} {m : ℕ} (M : OverlapModel d f m)

abbrev tr (k : ℕ) := (M.stage k).trace (M.decomposition k).weight

/-- Overlapping products are built, not postulated. -/
def product (u : (M.stage 0).Algebra) : ∀ k, (M.stage k).Algebra
  | 0 => u
  | k + 1 => M.left k (product u k) * M.right k u

lemma product_unitary {u : (M.stage 0).Algebra} (hu : (M.stage 0).IsUnitary u) :
    ∀ k, (M.stage k).IsUnitary (M.product u k)
  | 0 => hu
  | k + 1 => (M.stage (k + 1)).unitary_mul
      (Blocks.unitary_map (M.left k) (product_unitary hu k))
      (Blocks.unitary_map (M.right k) hu)

lemma tr_smul (k : ℕ) (z : ℂ) (u : (M.stage k).Algebra) :
    M.tr k (z • u) = z * M.tr k u := by
  simp only [tr, Blocks.trace, Pi.smul_apply, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Trace out the new block, using only bimodularity and the simple-strand
partial trace. This is the recurrence argued in Lemma 3.1. -/
lemma trace_product_succ (u : (M.stage 0).Algebra) (k : ℕ) :
    M.tr (k + 1) (M.product u (k + 1)) = M.tr k (M.product u k) * (M.tr 0 u / d) := by
  calc
    _ = M.tr k (M.partialTrace k (M.product u (k + 1))) := (M.trace_partial k _).symm
    _ = _ := by
      rw [product, M.partial_left, M.partial_right,
        mul_smul_comm, mul_one, M.tr_smul, mul_comm]

lemma trace_product (u : (M.stage 0).Algebra) (k : ℕ) :
    M.tr k (M.product u k) = (M.tr 0 u) ^ (k + 1) / (d : ℂ) ^ k := by
  induction k with
  | zero => simp [product]
  | succ k ih =>
    rw [trace_product_succ, ih, pow_succ, pow_succ]
    ring

/-- Paper Lemma 3.1, relative to the primitive spherical/semisimple interface.
In particular, neither its trace estimate nor its overlapping-product formula
is assumed by `OverlapModel`. -/
theorem trace_bound (hd : d ≠ 0) (hf : 0 < f)
    {u : (M.stage 0).Algebra} (hu : (M.stage 0).IsUnitary u) :
    ‖M.tr 0 u‖ ≤ |d| * f ^ (m - 1) := by
  apply trace_bound_of_overlap hd hf
  intro k
  have hupper : ‖M.tr k (M.product u k)‖ ≤ f ^ ((k + 1) * (m - 1) + 1) :=
    ((M.stage k).norm_trace_le (M.decomposition k).weight (M.product_unitary hu k)).trans
      ((M.decomposition k).mass_le_fpMass.trans_eq (M.fpMass_eq k))
  rw [M.trace_product u k, norm_div, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_eq_abs] at hupper
  have h := (div_le_iff₀ (pow_pos (abs_pos.mpr hd) k)).mp hupper
  simpa [mul_comm] using h

end OverlapModel
end PropertyF
