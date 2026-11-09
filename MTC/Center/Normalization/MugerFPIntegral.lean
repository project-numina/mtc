module
public import MTC.Center.Normalization.SymmetricSquares
public import MTC.Center.Normalization.MugerObjectNormalization

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Frobenius–Perron integrality of transparent objects, conditionally -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- In a pseudo-unitary symmetric category, every simple FP dimension is a
positive integer. -/
theorem symmetric_fpSimple_positive_integer_of_pseudoUnitary
    (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _)
    (hpu : PseudoUnitary C) (i : Fin (rank C)) :
    ∃ n : ℕ, 0 < n ∧ fpSimple C i = (n : ℝ) := by
  let p := canonicalSymmetricPivotal hsym
  have hsat := MTC.Center.Induction.pivotalDimension_norm_eq_fp_of_pseudoUnitary p hpu i
  let : Simple (simples C i) := simples_simple C i
  obtain ⟨m, hm⟩ := canonicalSymmetricPivotal_simple_integer C hsym (simples C i)
  change ‖pivotalDimension C p (simples C i)‖ = fpSimple C i at hsat
  have heq : fpSimple C i = (m.natAbs : ℝ) := by
    rw [← hsat, hm]
    simp [Complex.norm_intCast, ← Int.cast_abs]
  refine ⟨m.natAbs, ?_, heq⟩
  have := fpSimple_pos C i
  rw [heq] at this
  exact_mod_cast this

/-- Every object in a pseudo-unitary symmetric category has integer FP
dimension. -/
theorem symmetric_fpDimension_integer_of_pseudoUnitary
    (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _)
    (hpu : PseudoUnitary C) (X : C.Obj) :
    ∃ n : ℕ, fpDimension C X = (n : ℝ) := by
  classical
  choose d hd using symmetric_fpSimple_positive_integer_of_pseudoUnitary C hsym hpu
  refine ⟨∑ i, simpleMultiplicity C i X * d i, ?_⟩
  simp only [fpDimension, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z : ℝ => (simpleMultiplicity C i X : ℝ) * z) (hd i).2

set_option backward.isDefEq.respectTransparency false in
/-- If the actual Müger category is pseudo-unitary, all its actual objects
have integer FP dimension. -/
theorem muger_fpDimension_integer_of_pseudoUnitary
    (hpu : PseudoUnitary (bundledMuger C)) (X : MugerCategory C) :
    ∃ n : ℕ, fpDimension (bundledMuger C) X = (n : ℝ) :=
  symmetric_fpDimension_integer_of_pseudoUnitary (bundledMuger C)
    (mugerBraiding_symmetric C) hpu X

-- Retain the original pivotal parameter for callers; integrality follows from
-- the actual Müger category and does not depend on its choice.
set_option linter.unusedVariables false in
/-- If the actual Müger category is pseudo-unitary, every transparent object
has a nonnegative integer FP dimension. -/
theorem transparent_fpDimension_integer_of_muger_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary (bundledMuger C))
    (X : C.Obj) (hX : MTC.Center.Transparent X) :
    ∃ n : ℕ, fpDimension C X = (n : ℝ) := by
  let Y : MugerCategory C := ⟨X, hX⟩
  obtain ⟨n, hn⟩ := muger_fpDimension_integer_of_pseudoUnitary C hpu Y
  exact ⟨n, (muger_forget_fpDimension C Y).trans hn⟩

/-- In the same setting, every nonzero transparent object has positive
integer FP dimension. -/
theorem transparent_fpDimension_positive_integer_of_muger_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary (bundledMuger C))
    (X : C.Obj) (hX : MTC.Center.Transparent X) (hne : ¬ IsZero X) :
    ∃ n : ℕ, 0 < n ∧ fpDimension C X = (n : ℝ) := by
  obtain ⟨n, hn⟩ := transparent_fpDimension_integer_of_muger_pseudoUnitary C p hpu X hX
  refine ⟨n, ?_, hn⟩
  have hp := one_le_fpDimension hne
  rw [hn] at hp
  exact_mod_cast hp


end MTC.Center.Normalization
end
