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
  let : Simple (simples C i) := simples_simple C i
  rw [squaredNorm_eq_pivotalDimension_mul_dual (canonicalSymmetricPivotal hsym),
    pivotalDimension_simple_dual_conj (canonicalSymmetricPivotal hsym), hn i]
  simp [pow_two]

/-- The actual Müger centre has integer intrinsic global dimension. -/
theorem muger_globalDimension_integer :
    ∃ m : ℤ, globalDimension (bundledMuger C) = (m : ℂ) :=
  symmetric_globalDimension_integer (bundledMuger C) (mugerBraiding_symmetric C)

end MTC.Center.Normalization
end
