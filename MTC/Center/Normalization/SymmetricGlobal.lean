module
public import MTC.Center.Normalization.SymmetricInteger

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.Center.Induction

/-! # Integral intrinsic global dimension of symmetric fusion categories -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _)

include hsym in
/-- The intrinsic global dimension of a symmetric braided fusion category is
an integer, without assuming pseudo-unitarity. -/
theorem symmetric_globalDimension_integer :
    ∃ m : ℤ, globalDimension C = (m : ℂ) := by
  classical
  have h (i : Fin (rank C)) : ∃ n : ℤ,
      pivotalDimension C (canonicalSymmetricPivotal hsym) (simples C i) = (n : ℂ) := by
    let : Simple (simples C i) := simples_simple C i
    exact canonicalSymmetricPivotal_simple_integer C hsym (simples C i)
  choose n hn using h
  refine ⟨∑ i, n i ^ 2, ?_⟩
  rw [globalDimension]
  simp only [Int.cast_sum, Int.cast_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [squaredNorm_simple_eq_pivotalDimension_norm_sq (canonicalSymmetricPivotal hsym), hn i]
  simp [Complex.norm_intCast, sq_abs]

/-- The actual Müger centre has integer intrinsic global dimension. -/
theorem muger_globalDimension_integer :
    ∃ m : ℤ, globalDimension (bundledMuger C) = (m : ℂ) :=
  symmetric_globalDimension_integer (bundledMuger C) (mugerBraiding_symmetric C)

/-- If a pivotal fusion category has integer intrinsic global dimension,
that integer is strictly positive. -/
theorem globalDimension_positive_integer_of_integer
    (p : PivotalStructure (C := C.Obj))
    (h : ∃ m : ℤ, globalDimension C = (m : ℂ)) :
    ∃ n : ℕ, 0 < n ∧ globalDimension C = (n : ℂ) := by
  obtain ⟨m, hm⟩ := h
  have heq : (m : ℝ) = ∑ i : Fin (rank C), ‖pivotalDimension C p (simples C i)‖ ^ 2 := by
    apply Complex.ofReal_injective
    simpa using hm.symm.trans (globalDimension_eq_sum_pivotal_norm_sq p)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by
    rw [heq]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hmne : (m : ℝ) ≠ 0 := by
    intro hz
    apply globalDimension_ne_zero_of_pivotal p
    rw [hm]
    exact_mod_cast hz
  have hmpos : 0 < m := by exact_mod_cast lt_of_le_of_ne hm0 (Ne.symm hmne)
  refine ⟨m.toNat, ?_, ?_⟩
  · have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
    exact_mod_cast he.symm ▸ hmpos
  · rw [hm]
    have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
    exact_mod_cast he.symm

include hsym in
/-- The intrinsic global dimension of a symmetric braided fusion category is
a positive integer. -/
theorem symmetric_globalDimension_positive_integer :
    ∃ n : ℕ, 0 < n ∧ globalDimension C = (n : ℂ) :=
  globalDimension_positive_integer_of_integer C (canonicalSymmetricPivotal hsym)
    (symmetric_globalDimension_integer C hsym)

/-- The intrinsic global dimension of the actual Müger category is a positive
integer, without assuming pseudo-unitarity. -/
theorem muger_globalDimension_positive_integer :
    ∃ n : ℕ, 0 < n ∧ globalDimension (bundledMuger C) = (n : ℂ) :=
  symmetric_globalDimension_positive_integer (bundledMuger C) (mugerBraiding_symmetric C)

end MTC.Center.Normalization
end
