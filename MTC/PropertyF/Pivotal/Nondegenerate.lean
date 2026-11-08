module
public import MTC.PropertyF.Pivotal.FPGlobalDimension
public import MTC.PropertyF.Pivotal.Saturation

/-! # Frobenius–Perron self-monodromy

The FP column makes the actual normalized self-monodromy trace maximal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.Braided MTC.Braided.Trace MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- The FP-column label attains the monodromy trace bound. -/
theorem fp_column_self_monodromy_maximal (j : Fin (rank C))
    (hcolumn : ∀ i, categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ)) :
    ‖scalarTrace p (unitScalarEquiv C) (selfMonodromy (simples C j)) /
      pivotalDimension C p (simples C j)‖ = fpDimension C (simples C j) := by
  have hs : scalarTrace p (unitScalarEquiv C) (selfMonodromy (simples C j)) =
      categoricalS C p j j := by
    rfl
  rw [hs, hcolumn j, fpDimension_simple]
  change ‖simpleDimension C p j * (fpSimple C j : ℂ) / simpleDimension C p j‖ = _
  rw [mul_comm, mul_div_cancel_right₀ _ (simpleDimension_ne_zero C p j)]
  simp [Complex.norm_real, abs_of_pos (fpSimple_pos C j)]

/-- The FP-column object suffices: finite braid images of that one simple
object imply pseudo-unitarity and FP dimension one, whenever the actual
categorical S matrix is invertible. -/
theorem pseudoUnitary_of_fp_column_propertyF
    (hdet : (categoricalS C p).det ≠ 0) (j : Fin (rank C))
    (hcolumn : ∀ i, categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ))
    (hfinite : ObjectPropertyF (simples C j)) :
    PseudoUnitary C ∧ fpSimple C j = 1 := by
  let : Simple (simples C j) := simples_simple C j
  have hsat := pivotal_saturation C p hfinite (fp_column_self_monodromy_maximal C p j hcolumn)
  have hsat' : ‖simpleDimension C p j‖ = fpSimple C j := by
    simpa only [simpleDimension, fpDimension_simple] using hsat
  obtain ⟨k, ⟨hk, hdim⟩, _⟩ := existsUnique_fp_column_globalDimension C p hdet
  obtain ⟨t, _, hu⟩ := existsUnique_fp_column C p hdet
  have hkj : k = j := (hu k hk).trans (hu j hcolumn).symm
  subst k
  exact pseudoUnitary_of_fp_column_saturation C p j hdim hsat'

/-- Property F implies pseudo-unitarity for any pivotal braided fusion
category with invertible actual categorical S matrix. -/
theorem pseudoUnitary_of_invertibleS_of_propertyF
    (hdet : (categoricalS C p).det ≠ 0) (hF : HasPropertyF C.Obj) :
    PseudoUnitary C := by
  obtain ⟨j, hj, _⟩ := existsUnique_fp_column C p hdet
  exact (pseudoUnitary_of_fp_column_propertyF C p hdet j hj (hF _)).1

end MTC.PropertyF.Pivotal
