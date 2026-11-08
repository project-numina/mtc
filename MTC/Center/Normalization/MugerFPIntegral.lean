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

/-- In a pseudo-unitary symmetric category, every simple FP dimension is a
positive integer. -/
theorem symmetric_fpSimple_positive_integer_of_pseudoUnitary
    (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _)
    (hpu : PseudoUnitary C) (i : Fin (rank C)) :
    ∃ n : ℕ, 0 < n ∧ fpSimple C i = (n : ℝ) := by
  let p := canonicalSymmetricPivotal hsym
  let d (j : Fin (rank C)) := pivotalDimension C p (simples C j)
  have hbound (j : Fin (rank C)) : ‖d j‖ ≤ fpSimple C j :=
    character_norm_le_fpSimple (C := C) (i₀ := unitIndex C)
      ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
      (pivotalDimension_character C p) j
  have hnorm (j : Fin (rank C)) : squaredNorm C (simples C j) = ((‖d j‖ ^ 2 : ℝ) : ℂ) := by
    let : Simple (simples C j) := simples_simple C j
    rw [MTC.Center.Induction.squaredNorm_eq_pivotalDimension_mul_dual p,
      MTC.Center.Induction.pivotalDimension_simple_dual_conj (C := C) p]
    simpa only [d, Complex.star_def, Complex.ofReal_pow] using
      Complex.mul_conj' (pivotalDimension C p (simples C j))
  have hsat := norm_saturation_of_pseudoUnitary hbound hnorm hpu i
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

end MTC.Center.Normalization
end
