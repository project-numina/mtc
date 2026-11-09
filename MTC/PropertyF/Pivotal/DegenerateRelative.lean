module
public import MTC.PropertyF.Pivotal.DegenerateConsequences
public import MTC.Center.Normalization.RelativeCentralizer

/-! # Degenerate theorem reduced to relative numerical centrality -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "Z" => MTC.PropertyF.Reduction.bundledCenter C

/-- The full degenerate conclusion follows from the manuscript's hypotheses,
centre S invertibility and the relative numerical-to-actual centrality test
for the actual product-image fusion subcategory of the centre. -/
theorem degenerate_conclusions_of_relative_center_criterion
    (p : PivotalStructure (C := C.Obj))
    (hpositive : PositiveOnTransparentAdjoint C p)
    (hdet : ∀ pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj),
      (categoricalS Z pZ).det ≠ 0)
    (hrelative : ∀ (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
      (y : Fin (rank Z)),
      (∀ a ∈ MTC.Center.Braid.productLabels C, sCentralizes Z pZ a y) →
      ∀ a ∈ MTC.Center.Braid.productLabels C,
        doubleBraiding (simples Z a) (simples Z y) = 𝟙 _)
    (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
      WeaklyIntegral (globalFPDimension C) := by
  obtain ⟨q, hq⟩ := normalizationStatement_proved C p hpositive
  let pZ := MTC.Center.Induction.liftedPivotalStructure q
    (MTC.Center.Induction.pivotalComponentsCentral_proved q)
  have hpu := pseudoUnitary_of_normalized_muger_and_center_criteria C q pZ
    (fun W ↦ MTC.Center.Induction.liftedPivotalStructure_compatible _ W)
    (hdet pZ) hF
    (MTC.Center.Normalization.productNumericalCentralizer_subset_symmetricCore_of_relative C
      (hrelative pZ)) hq
  exact all_conclusions_of_pseudoUnitary_of_propertyF C hpu hF

end MTC.PropertyF.Pivotal
end
