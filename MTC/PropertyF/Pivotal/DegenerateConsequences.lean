module
public import MTC.PropertyF.Pivotal.CenterAdjointReduction
public import MTC.PropertyF.Pivotal.ConjugateCorollary
public import MTC.PropertyF.PseudoUnitary
public import MTC.Center.Normalization.PositiveSubring

/-! # Consequences of the pivotal centre reduction

The centre criteria below are explicit intermediate assumptions. They are not
part of the manuscript's degenerate theorem; `MainTheorems` discharges them.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u

/-- The manuscript's normalization lemma holds with exactly its stated
transparent-adjoint positivity hypothesis. -/
theorem normalizationStatement_proved : NormalizationStatement.{v,u} := by
  intro C p hpositive
  exact MTC.Center.Normalization.normalize_pivotal_on_muger_of_adjoint_positivity_unconditional
    C p hpositive

/-- Property F upgrades pseudo-unitarity to all Galois conjugates and weak
integrality. -/
theorem all_conclusions_of_pseudoUnitary_of_propertyF
    (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C)
    (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
      WeaklyIntegral (globalFPDimension C) := by
  have hw := MTC.PropertyF.weaklyIntegral_of_propertyF_of_pseudoUnitary C hpu hF
  exact ⟨hpu, allGaloisConjugatesPseudoUnitary_of_pseudoUnitary_of_weaklyIntegral C hpu hw, hw⟩

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "Z" => MTC.PropertyF.Reduction.bundledCenter C

/-- The full degenerate conclusion, conditional on the stated centre
S-matrix criteria and transparent dimension saturation. -/
theorem degenerate_conclusions_of_center_criteria
    (p : PivotalStructure (C := C.Obj))
    (hpositive : PositiveOnTransparentAdjoint C p)
    (hsat : ∀ i, MTC.Center.Transparent (simples C i) →
      ‖pivotalDimension C p (simples C i)‖ = fpSimple C i)
    (hdet : ∀ pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj), (categoricalS Z pZ).det ≠ 0)
    (hcriterion : ∀ (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
      (a : Fin (rank Z)) (_ha : a ∈ MTC.Center.Braid.imageLabels C)
      (y : Fin (rank Z)), sCentralizes Z pZ a y →
        doubleBraiding (simples Z a) (simples Z y) = 𝟙 _)
    (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
      WeaklyIntegral (globalFPDimension C) :=
  all_conclusions_of_pseudoUnitary_of_propertyF C
    (pseudoUnitary_of_adjoint_positivity_and_center_criteria C p hpositive hsat hdet hcriterion hF) hF

/-- The complete degenerate conclusion from adjoint positivity and property F,
conditional on the two centre S-matrix criteria alone. -/
theorem degenerate_conclusions_of_S_criteria
    (p : PivotalStructure (C := C.Obj))
    (hpositive : PositiveOnTransparentAdjoint C p)
    (hdet : ∀ pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj),
      (categoricalS Z pZ).det ≠ 0)
    (hcriterion : ∀ (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
      (a : Fin (rank Z)) (_ha : a ∈ MTC.Center.Braid.imageLabels C)
      (y : Fin (rank Z)), sCentralizes Z pZ a y →
        doubleBraiding (simples Z a) (simples Z y) = 𝟙 _)
    (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
      WeaklyIntegral (globalFPDimension C) :=
  degenerate_conclusions_of_center_criteria C p hpositive
    (MTC.Center.Normalization.transparent_norm_saturation_of_adjoint_positivity C p hpositive)
    hdet hcriterion hF

end MTC.PropertyF.Pivotal
end
