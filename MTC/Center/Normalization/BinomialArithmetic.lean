module
public import MTC.Center.Normalization.BinomialAnalytic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Arithmetic of paired generalized binomials -/

@[expose] public noncomputable section
open scoped BigOperators IntermediateField
open Filter
namespace MTC.Center.Normalization

/-- The paired generalized binomial in a characteristic-zero field. -/
def pairedBinomialField {K : Type*} [Field K] (a : K) (n : ℕ) : K :=
  (∏ k ∈ Finset.range n, (a ^ 2 - (k : K) ^ 2)) / ((n.factorial : K) ^ 2)

/-- Field embeddings preserve paired generalized binomials. -/
theorem map_pairedBinomialField {K : Type*} [Field K] (φ : K →+* ℂ) (a : K) (n : ℕ) :
    φ (pairedBinomialField a n) = pairedBinomial (φ a) n := by
  simp [pairedBinomialField, pairedBinomial, map_div₀]

/-- An element whose paired generalized binomials are all algebraic integers
is a rational integer. -/
theorem integer_of_integral_pairedBinomial {K : Type*} [Field K] [NumberField K]
    (φ₀ : K →+* ℂ) (a : K) (hint : ∀ n, IsIntegral ℤ (pairedBinomialField a n)) :
    ∃ m : ℤ, a = m := by
  have hevent : ∀ᶠ n in atTop, ∀ φ : K →+* ℂ, ‖φ (pairedBinomialField a n)‖ < 1 := by
    apply Filter.eventually_all.mpr
    intro φ
    have h := (pairedBinomial_tendsto_zero (φ a)).norm
    have h' : ∀ᶠ n in atTop, ‖pairedBinomial (φ a) n‖ < 1 := by
      exact h.eventually (Iio_mem_nhds (by norm_num))
    simpa only [map_pairedBinomialField] using h'
  obtain ⟨n, hn⟩ := hevent.exists
  have hzero : pairedBinomialField a n = 0 := by
    by_contra hne
    obtain ⟨m, hm, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hne
      (hint n) (fun φ => le_of_lt (hn φ))
    have hp' : ‖φ₀ (pairedBinomialField a n)‖ ^ m = 1 := by
      have heq := congrArg φ₀ hp
      have heq' := congrArg norm heq
      simpa using heq'
    have hlt := pow_lt_one₀ (norm_nonneg (φ₀ (pairedBinomialField a n))) (hn φ₀) (ne_of_gt hm)
    exact (ne_of_lt hlt) hp'
  have hp : (∏ k ∈ Finset.range n, (a ^ 2 - (k : K) ^ 2)) = 0 := by
    have hd : ((n.factorial : K) ^ 2) ≠ 0 := by
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    exact (div_eq_zero_iff.mp hzero).resolve_right hd
  obtain ⟨k, hk, hz⟩ := Finset.prod_eq_zero_iff.mp hp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp hz) with h | h
  · exact ⟨k, by simpa using h⟩
  · exact ⟨-(k : ℤ), by simpa using h⟩

/-- Paired binomials are products of the falling and rising binomials. -/
theorem pairedBinomial_eq_falling_mul_rising (z : ℂ) (n : ℕ) :
    pairedBinomial z n =
      ((∏ k ∈ Finset.range n, (z - (k : ℂ))) / (n.factorial : ℂ)) *
      ((∏ k ∈ Finset.range n, (z + (k : ℂ))) / (n.factorial : ℂ)) := by
  rw [pairedBinomial, div_mul_div_comm, ← Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    ring
  · ring

/-- If all falling and rising generalized binomials of a complex algebraic
integer are algebraic integers, then the parameter is an integer. -/
theorem integer_of_integral_falling_rising (z : ℂ) (hz : IsIntegral ℤ z)
    (hfall : ∀ n : ℕ, IsIntegral ℤ
      ((∏ k ∈ Finset.range n, (z - (k : ℂ))) / (n.factorial : ℂ)))
    (hrise : ∀ n : ℕ, IsIntegral ℤ
      ((∏ k ∈ Finset.range n, (z + (k : ℂ))) / (n.factorial : ℂ))) :
    ∃ m : ℤ, z = m := by
  let K := ℚ⟮z⟯
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hz.tower_top
  let : NumberField K := ⟨⟩
  let a : K := ⟨z, IntermediateField.mem_adjoin_simple_self ℚ z⟩
  let φ : K →+* ℂ := algebraMap K ℂ
  have hmap (n : ℕ) : IsIntegral ℤ (φ (pairedBinomialField a n)) := by
    rw [map_pairedBinomialField, pairedBinomial_eq_falling_mul_rising]
    exact (hfall n).mul (hrise n)
  have hint (n : ℕ) : IsIntegral ℤ (pairedBinomialField a n) :=
    isIntegral_algebraMap_iff.mp (hmap n)
  obtain ⟨m, hm⟩ := integer_of_integral_pairedBinomial φ a hint
  refine ⟨m, ?_⟩
  have := congrArg φ hm
  simpa [φ, a] using this

end MTC.Center.Normalization
end
