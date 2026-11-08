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

/-- If the actual Müger category is pseudo-unitary, every transparent object
has a nonnegative integer FP dimension. -/
theorem transparent_fpDimension_integer_of_muger_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary (bundledMuger C))
    (X : C.Obj) (hX : MTC.Center.Transparent X) :
    ∃ n : ℕ, fpDimension C X = (n : ℝ) := by
  classical
  let d : Fin (rank C) → ℕ := fun i =>
    if hi : MTC.Center.Transparent (simples C i) then
      Classical.choose (transparent_fpSimple_positive_integer_of_muger_pseudoUnitary C p hpu i hi)
    else 0
  refine ⟨∑ i, simpleMultiplicity C i X * d i, ?_⟩
  simp only [fpDimension, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : simpleMultiplicity C i X = 0
  · simp [hz]
  · have ht := transparent_simple_of_positive_multiplicity C X hX i (Nat.pos_of_ne_zero hz)
    have he := (Classical.choose_spec
      (transparent_fpSimple_positive_integer_of_muger_pseudoUnitary C p hpu i ht)).2
    simp only [d, dite_eq_left ht]
    exact congrArg (fun z : ℝ => (simpleMultiplicity C i X : ℝ) * z) he

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
