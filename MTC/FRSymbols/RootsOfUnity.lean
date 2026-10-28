module
public import MTC.FRSymbols.Cyclotomic
public import Mathlib.Tactic

/-!
# A cyclotomic phase certificate

The polynomial identity below simplifies a power-basis coefficient occurring
in a locally downloaded B11-00119 R block. It applies to every primitive 70th
root in a field and does not depend on any downloaded file. The downloaded
block can be identified with its left side by the generated Lean definitions.
-/

@[expose] public section
namespace MTC.FRSymbols

/-- A useful exact simplification in the power basis of a primitive 70th root. -/
theorem primitive_seventy_phase {K : Type*} [Field K] (z : K) (hz : IsPrimitiveRoot z 70) :
    z - z ^ 8 + z ^ 15 - z ^ 22 = z ^ 64 := by
  have h35sq : (z ^ 35) ^ 2 = 1 := by
    simpa only [← pow_mul] using hz.pow_eq_one
  have h35ne : z ^ 35 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  have h35 : z ^ 35 = -1 := by
    rcases (sq_eq_one_iff).mp h35sq with h | h
    · exact False.elim (h35ne h)
    · exact h
  have h7ne : z ^ 7 + 1 ≠ 0 := by
    intro h
    have hz7 : z ^ 7 = -1 := by linear_combination h
    have h14 : z ^ 14 = 1 := by
      calc
        z ^ 14 = (z ^ 7) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hz7]; ring
    exact (hz.pow_ne_one_of_pos_of_lt (by decide : 14 ≠ 0) (by decide : 14 < 70)) h14
  have hfactor : z ^ 28 - z ^ 21 + z ^ 14 - z ^ 7 + 1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left h7ne
    calc
      (z ^ 7 + 1) * (z ^ 28 - z ^ 21 + z ^ 14 - z ^ 7 + 1) = z ^ 35 + 1 := by ring
      _ = 0 := by rw [h35]; ring
  have h64 : z ^ 64 = -z ^ 29 := by
    calc
      z ^ 64 = z ^ 35 * z ^ 29 := by rw [← pow_add]
      _ = -z ^ 29 := by rw [h35]; ring
  rw [h64]
  have hzero : z - z ^ 8 + z ^ 15 - z ^ 22 + z ^ 29 = 0 := by
    calc
      _ = z * (z ^ 28 - z ^ 21 + z ^ 14 - z ^ 7 + 1) := by ring
      _ = 0 := by rw [hfactor]; ring
  linear_combination hzero

/-- The corresponding coefficient has modulus one in the standard complex embedding. -/
theorem cyclotomic_seventy_phase_unitary :
    Complex.normSq (cyclotomicEmbedding 70
      (cyclotomicGenerator 70 - cyclotomicGenerator 70 ^ 8 +
        cyclotomicGenerator 70 ^ 15 - cyclotomicGenerator 70 ^ 22)) = 1 := by
  rw [primitive_seventy_phase _ (cyclotomicGenerator_primitive 70), map_pow,
    cyclotomicEmbedding_generator, Complex.normSq_eq_norm_sq, norm_pow,
    (Complex.isPrimitiveRoot_exp 70 (by decide)).norm'_eq_one (by decide)]
  norm_num

end MTC.FRSymbols
