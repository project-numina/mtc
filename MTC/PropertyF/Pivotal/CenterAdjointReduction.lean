module
public import MTC.PropertyF.Pivotal.CenterReduction
public import MTC.PropertyF.Pivotal.Statement
public import MTC.Center.Normalization.MugerAdjointNormalization

/-! # Adjoint-positivity reduction for the pivotal centre argument

This is a conditional intermediate result. The symmetric-centre FP norm
saturation and the two centre S-matrix criteria are explicit premises.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "Z" => MTC.PropertyF.Reduction.bundledCenter C

/-- Adjoint positivity and property F imply pseudo-unitarity once transparent
FP-norm saturation and the centre's S-matrix criteria have been established.
All three intermediate categorical inputs are visible in the statement. -/
theorem pseudoUnitary_of_adjoint_positivity_and_center_criteria
    (p : PivotalStructure (C := C.Obj))
    (hpositive : PositiveOnTransparentAdjoint C p)
    (hsat : ∀ i, MTC.Center.Transparent (simples C i) →
      ‖pivotalDimension C p (simples C i)‖ = fpSimple C i)
    (hdet : ∀ pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj), (categoricalS Z pZ).det ≠ 0)
    (hcriterion : ∀ (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
      (a : Fin (rank Z)) (_ha : a ∈ MTC.Center.Braid.imageLabels C)
      (y : Fin (rank Z)),
      sCentralizes Z pZ a y →
        doubleBraiding (simples Z a) (simples Z y) = 𝟙 _)
    (hF : HasPropertyF C.Obj) : PseudoUnitary C := by
  obtain ⟨q, hq⟩ := MTC.Center.Normalization.normalize_pivotal_on_muger_of_adjoint_positivity
    C p hsat hpositive
  let pZ := MTC.Center.Induction.liftedPivotalStructure q
    (MTC.Center.Induction.pivotalComponentsCentral_proved q)
  apply pseudoUnitary_of_normalized_muger_and_simple_criterion C q pZ
    (fun W ↦ MTC.Center.Induction.liftedPivotalStructure_compatible _ W)
    (hdet pZ) hF (hcriterion pZ)
  exact hq

end MTC.PropertyF.Pivotal
end
