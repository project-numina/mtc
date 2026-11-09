module
public import MTC.Center.Induction.PivotalSquare

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.PropertyF.Reduction

/-! # Integer pivotal dimensions and the actual centre

These are elementary prerequisites for the symmetric-category pseudo-unitarity
argument. Integer dimensions of a symmetric category are not proved here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Center.Normalization
universe v u
variable {C : BraidedFusionCategory.{v,u}}

/-- Integer pivotal dimensions on simple representatives imply integer
pivotal dimensions on every object. -/
theorem pivotalDimension_integer_of_simple_integers
    (p : PivotalStructure (C := C.Obj))
    (h : ∀ i, ∃ z : ℤ, pivotalDimension C p (simples C i) = (z : ℂ))
    (X : C.Obj) : ∃ z : ℤ, pivotalDimension C p X = (z : ℂ) := by
  classical
  choose n hn using h
  refine ⟨∑ i, (simpleMultiplicity C i X : ℤ) * n i, ?_⟩
  rw [pivotalDimension_decomposition C p]
  simp [hn]

/-- Integer pivotal dimensions pass to the actual Drinfeld centre under a
compatible pivotal lift. -/
theorem center_pivotalDimension_integer_of_base
    [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, MTC.Center.Induction.PivotalCompatibleAt p pZ Z)
    (h : ∀ i, ∃ z : ℤ, pivotalDimension C p (simples C i) = (z : ℂ))
    (Z : Center C.Obj) : ∃ z : ℤ,
      pivotalDimension (bundledCenter C) pZ Z = (z : ℂ) := by
  rw [MTC.Center.Induction.center_pivotalDimension_forget (hcompat Z)]
  exact pivotalDimension_integer_of_simple_integers p h Z.1


/-- Integer simple pivotal dimensions force pseudo-unitarity when the actual
centre has a compatible pivotal FP column with the displayed Hermitian norm
identity. This is a conditional centre-FP reduction, not a proof of symmetric
category integrality or centre nondegeneracy. -/
theorem pseudoUnitary_of_integer_dimensions_and_center_fp_orthogonality
    [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, MTC.Center.Induction.PivotalCompatibleAt p pZ Z)
    (hint : ∀ i, ∃ z : ℤ, pivotalDimension C p (simples C i) = (z : ℂ))
    {j : Fin (rank (bundledCenter C))}
    (hcol : ∀ i, MTC.Modular.categoricalS (bundledCenter C) pZ i j =
      pivotalDimension (bundledCenter C) pZ (simples (bundledCenter C) j) *
        (fpSimple (bundledCenter C) i : ℂ))
    (hgram : (∑ i, star (MTC.Modular.categoricalS (bundledCenter C) pZ i j) *
      MTC.Modular.categoricalS (bundledCenter C) pZ i j) = globalDimension (bundledCenter C)) :
    PseudoUnitary C := by
  let Z := bundledCenter C
  let d : ℂ := pivotalDimension Z pZ (simples Z j)
  let r : ℝ := ∑ i : Fin (rank C), ‖pivotalDimension C p (simples C i)‖ ^ 2
  have hr : 0 ≤ r := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hf : 0 < globalFPDimension C :=
    lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  have hupper : r ≤ globalFPDimension C := by
    simpa only [MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq p,
      Complex.ofReal_re] using
      MTC.PropertyF.Pivotal.globalDimension_re_le_globalFPDimension C p
  obtain ⟨n, hn⟩ := center_pivotalDimension_integer_of_base hcompat hint (simples Z j)
  change d = (n : ℂ) at hn
  have hdne : d ≠ 0 := MTC.Modular.simpleDimension_ne_zero Z pZ j
  have hnne : n ≠ 0 := by
    intro hz
    apply hdne
    simpa [hz, d] using hn
  have hone : 1 ≤ ‖d‖ := by
    rw [hn]
    simpa [Complex.norm_intCast, ← Int.cast_abs] using
      (show (1 : ℝ) ≤ (|n| : ℝ) by exact_mod_cast Int.one_le_abs hnne)
  have hgram' : globalDimension Z = ((‖d‖ ^ 2 : ℝ) : ℂ) * (globalFPDimension Z : ℂ) :=
    globalDimension_eq_norm_sq_mul_fp_of_gram_column (C := Z) (j := j) pZ hcol hgram
  have hdim : globalDimension C = (r : ℂ) :=
    MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq p
  rw [MTC.Center.Induction.globalDimension_square_of_pivotal p,
    MTC.Center.Induction.globalFPDimension_square_of_actual_induction C, hdim] at hgram'
  have hsquare : r ^ 2 = ‖d‖ ^ 2 * globalFPDimension C ^ 2 := by
    exact_mod_cast hgram'
  have hnormsq : (1 : ℝ) ≤ ‖d‖ ^ 2 := by nlinarith [norm_nonneg d]
  have hsq : globalFPDimension C ^ 2 ≤ r ^ 2 := by
    rw [hsquare]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hnormsq
      (sq_nonneg (globalFPDimension C))
  have heq : r = globalFPDimension C :=
    le_antisymm hupper ((sq_le_sq₀ hf.le hr).mp hsq)
  change globalDimension C = (globalFPDimension C : ℂ)
  rw [hdim, heq]

end MTC.Center.Normalization
end
