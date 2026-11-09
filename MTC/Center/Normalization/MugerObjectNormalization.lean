module
public import MTC.Center.Normalization.MugerConditional

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Normalization on all transparent objects -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A simple with positive multiplicity in a transparent object is itself
transparent. -/
theorem transparent_simple_of_positive_multiplicity
    (X : C.Obj) (hX : MTC.Center.Transparent X) (i : Fin (rank C))
    (hi : 0 < simpleMultiplicity C i X) : MTC.Center.Transparent (simples C i) :=
  muger_piece_transparent C ⟨X, hX⟩ ⟨i, ⟨0, hi⟩⟩

/-- Normalization on transparent simple representatives extends to every actual
transparent object by semisimplicity. -/
theorem pivotalDimension_eq_fp_of_transparent
    (p : PivotalStructure (C := C.Obj))
    (hnorm : ∀ i, MTC.Center.Transparent (simples C i) →
      pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (X : C.Obj) (hX : MTC.Center.Transparent X) :
    pivotalDimension C p X = (fpDimension C X : ℂ) := by
  rw [pivotalDimension_decomposition]
  simp only [fpDimension, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : simpleMultiplicity C i X = 0
  · simp [hz]
  · rw [hnorm i (transparent_simple_of_positive_multiplicity C X hX i (Nat.pos_of_ne_zero hz))]

/-- Under pseudo-unitarity of the actual Müger category, adjoint positivity
normalizes pivotal dimensions on every transparent object. -/
theorem normalize_pivotal_all_transparent_of_muger_pseudoUnitary
    (p : PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary (bundledMuger C))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ X : C.Obj,
      MTC.Center.Transparent X → pivotalDimension C q X = (fpDimension C X : ℂ) := by
  obtain ⟨q, hq⟩ :=
    normalize_pivotal_of_muger_pseudoUnitary_and_adjoint_positivity C p hpu hpositive
  exact ⟨q, fun X hX => pivotalDimension_eq_fp_of_transparent C q hq X hX⟩

set_option backward.isDefEq.respectTransparency false in
/-- Adjoint positivity normalizes pivotal dimensions on every transparent
object when the actual Müger category's Drinfeld centre has invertible S. -/
theorem normalize_pivotal_all_transparent_of_muger_center_S_invertible
    [RigidCategory (Center (bundledMuger C).Obj)]
    [IsFusionCategory (Center (bundledMuger C).Obj)]
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r)
    (hdet : (MTC.Modular.categoricalS
      (MTC.PropertyF.Reduction.bundledCenter (bundledMuger C))
      (MTC.Center.Induction.liftedPivotalStructure
        (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))
        (MTC.Center.Induction.pivotalComponentsCentral_proved
          (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))))).det ≠ 0) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ X : C.Obj,
      MTC.Center.Transparent X → pivotalDimension C q X = (fpDimension C X : ℂ) :=
  normalize_pivotal_all_transparent_of_muger_pseudoUnitary C p
    (muger_pseudoUnitary_of_center_S_invertible C hdet) hpositive

end MTC.Center.Normalization
end
