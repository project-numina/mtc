module
public import MTC.Center.Normalization.SymmetricGlobal

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Modular

/-! # Squared norms in symmetric fusion categories -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (hsym : ∀ X Y : C.Obj, doubleBraiding X Y = 𝟙 _)

include hsym in
/-- Every simple squared norm in a symmetric fusion category is the square of
a positive integer, without a pseudo-unitarity hypothesis. -/
theorem symmetric_simple_squaredNorm_positive_square (i : Fin (rank C)) :
    ∃ n : ℕ, 0 < n ∧ squaredNorm C (simples C i) = (n : ℂ) ^ 2 := by
  let : Simple (simples C i) := simples_simple C i
  obtain ⟨m, hm⟩ := canonicalSymmetricPivotal_simple_integer C hsym (simples C i)
  have hmne : m ≠ 0 := by
    intro hz
    have hd := simpleDimension_ne_zero C (canonicalSymmetricPivotal hsym) i
    apply hd
    simpa [simpleDimension, hz] using hm
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hmne, ?_⟩
  rw [squaredNorm_eq_pivotalDimension_mul_dual (canonicalSymmetricPivotal hsym),
    pivotalDimension_simple_dual_conj (canonicalSymmetricPivotal hsym), hm]
  have habs : ((m.natAbs : ℂ) ^ 2) = (m : ℂ) ^ 2 := by
    have h : (m.natAbs : ℤ) ^ 2 = m ^ 2 := by simp
    simpa only [Int.cast_pow, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℂ)) h
  rw [habs]
  simp [pow_two]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A transparent simple of an arbitrary pivotal braided fusion category has
intrinsic squared norm equal to a positive integer square. -/
theorem transparent_simple_squaredNorm_positive_square
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C))
    (hi : MTC.Center.Transparent (simples C i)) :
    ∃ n : ℕ, 0 < n ∧ squaredNorm C (simples C i) = (n : ℂ) ^ 2 := by
  let M := bundledMuger C
  let X : MugerCategory C := mugerSimple C ⟨i, (mem_mugerLabels C i).mpr hi⟩
  let : Simple X := mugerSimple_simple C _
  let : Simple (simples C i) := simples_simple C i
  obtain ⟨j, ⟨e⟩⟩ := exists_simple_iso M X
  obtain ⟨n, hn, hsq⟩ := symmetric_simple_squaredNorm_positive_square M
    (mugerBraiding_symmetric C) j
  refine ⟨n, hn, ?_⟩
  have he : squaredNorm M (simples M j) = squaredNorm C (simples C i) := by
    let : Simple (simples M j) := simples_simple M j
    rw [squaredNorm_eq_pivotalDimension_mul_dual (mugerPivotal C p),
      pivotalDimension_simple_dual_conj (C := M) (mugerPivotal C p)]
    rw [← pivotalDimension_iso (C := M) (mugerPivotal C p) e,
      muger_pivotalDimension_forget]
    rw [squaredNorm_eq_pivotalDimension_mul_dual p, pivotalDimension_simple_dual_conj p]
    rfl
  exact he.symm.trans hsq

/-- The norm of the pivotal dimension of a transparent simple is a positive
integer, for any pivotal structure on the ambient braided fusion category. -/
theorem transparent_simple_pivotal_norm_positive_integer
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C))
    (hi : MTC.Center.Transparent (simples C i)) :
    ∃ n : ℕ, 0 < n ∧ ‖pivotalDimension C p (simples C i)‖ = (n : ℝ) := by
  obtain ⟨n, hn, hsq⟩ := transparent_simple_squaredNorm_positive_square C p i hi
  let : Simple (simples C i) := simples_simple C i
  rw [squaredNorm_eq_pivotalDimension_mul_dual p, pivotalDimension_simple_dual_conj p] at hsq
  have hreal : ‖pivotalDimension C p (simples C i)‖ ^ 2 = (n : ℝ) ^ 2 := by
    have hnorm := Complex.mul_conj' (pivotalDimension C p (simples C i))
    rw [show star (pivotalDimension C p (simples C i)) =
      starRingEnd ℂ (pivotalDimension C p (simples C i)) from rfl, hnorm] at hsq
    exact_mod_cast hsq
  refine ⟨n, hn, ?_⟩
  nlinarith [norm_nonneg (pivotalDimension C p (simples C i)), Nat.cast_nonneg (α := ℝ) n]

/-- If the actual Müger category is pseudo-unitary, every transparent simple
has positive integer Frobenius–Perron dimension. -/
theorem transparent_fpSimple_positive_integer_of_muger_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary (bundledMuger C))
    (i : Fin (rank C)) (hi : MTC.Center.Transparent (simples C i)) :
    ∃ n : ℕ, 0 < n ∧ fpSimple C i = (n : ℝ) := by
  obtain ⟨n, hn, hnorm⟩ := transparent_simple_pivotal_norm_positive_integer C p i hi
  rw [transparent_norm_saturation_of_muger_pseudoUnitary C p hpu i hi] at hnorm
  exact ⟨n, hn, hnorm⟩

end MTC.Center.Normalization
end
