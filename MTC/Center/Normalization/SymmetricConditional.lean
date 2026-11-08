module
public import MTC.Center.Normalization.SymmetricInteger
public import MTC.PropertyF.Pivotal.SOrthogonality

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open MTC.Center.Induction MTC.PropertyF.Pivotal MTC.Modular MTC.PropertyF.Reduction

/-! # Symmetric pseudo-unitarity from centre S invertibility

The invertibility of the actual centre S matrix is explicitly assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (hsym : ∀ X Y : C.Obj, doubleBraiding X Y = 𝟙 _)
variable [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]

set_option backward.isDefEq.respectTransparency false in
/-- A symmetric fusion category is pseudo-unitary if its actual Drinfeld
centre's categorical S matrix is invertible. -/
theorem symmetric_pseudoUnitary_of_center_S_invertible
    (hdet : (categoricalS (bundledCenter C)
      (liftedPivotalStructure (canonicalSymmetricPivotal hsym)
        (pivotalComponentsCentral_proved (canonicalSymmetricPivotal hsym)))).det ≠ 0) :
    PseudoUnitary C := by
  let p := canonicalSymmetricPivotal hsym
  let pZ := liftedPivotalStructure p (pivotalComponentsCentral_proved p)
  obtain ⟨j, hj, _⟩ := existsUnique_fp_column (bundledCenter C) pZ hdet
  apply pseudoUnitary_of_integer_dimensions_and_center_fp_orthogonality
    (p := p) (pZ := pZ) (j := j)
  · exact liftedPivotalStructure_compatible (pivotalComponentsCentral_proved p)
  · intro i
    let : Simple (simples C i) := simples_simple C i
    exact canonicalSymmetricPivotal_simple_integer C hsym (simples C i)
  · exact hj
  · change (∑ i, starRingEnd ℂ (categoricalS (bundledCenter C) pZ i j) *
      categoricalS (bundledCenter C) pZ i j) = globalDimension (bundledCenter C)
    rw [categoricalS_column_length (bundledCenter C) pZ hdet j,
      globalDimension_eq_sum_pivotal_norm_sq pZ]
    simp only [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change star (pivotalDimension (bundledCenter C) pZ (simples (bundledCenter C) i)) * _ = _
    simpa [Complex.star_def, Complex.ofReal_pow] using
      (Complex.conj_mul' (pivotalDimension (bundledCenter C) pZ (simples (bundledCenter C) i)))


end MTC.Center.Normalization
end
