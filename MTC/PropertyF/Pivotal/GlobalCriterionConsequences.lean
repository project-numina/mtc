module
public import MTC.PropertyF.Pivotal.RelativeCriterionConsequences
public import MTC.Center.Rigid
public import MTC.Center.Induction.PivotalFusion

/-! # Manuscript targets reduced to relative fusion centrality

The relative numerical-to-actual criterion is an explicit, unproved
categorical premise in these two reductions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions MTC.Center.Braid
namespace MTC.PropertyF.Pivotal
universe v u

/-- The main nondegenerate statement follows from the relative numerical
centrality criterion in the ambient category. -/
theorem nondegenerateStatement_of_relative_fusion_criterion
    (hrelative : ∀ (D : BraidedFusionCategory.{v,u})
      (p : PivotalStructure (C := D.Obj))
      (A : Finset (Fin (rank D))), IsFusionSubring D A → ∀ y : Fin (rank D),
      (∀ a ∈ A, sCentralizes D p a y) →
      ∀ a ∈ A, doubleBraiding (simples D a) (simples D y) = 𝟙 _) :
    NondegenerateMainStatement.{v,u} := by
  intro C ⟨p⟩ hn hF
  apply main_of_nondegenerate_of_numerical_transparency C p hn
  · intro k hk
    apply transparent_of_simple_monodromy C k
    intro i
    exact hrelative C p Finset.univ (univ_isFusionSubring C) k
      (fun a _ => hk a) i (Finset.mem_univ i)
  · exact hF

/-- The degenerate statement follows from the same relative numerical
centrality criterion. The centre rigidity and fusion structures are
constructed from the given pivotal category. -/
theorem degenerateStatement_of_relative_fusion_criterion
    (hrelative : ∀ (D : BraidedFusionCategory.{v,max v u})
      (p : PivotalStructure (C := D.Obj))
      (A : Finset (Fin (rank D))), IsFusionSubring D A → ∀ y : Fin (rank D),
      (∀ a ∈ A, sCentralizes D p a y) →
      ∀ a ∈ A, doubleBraiding (simples D a) (simples D y) = 𝟙 _) :
    DegenerateMainStatement.{v,u} := by
  intro C p hpositive hF
  letI : RigidCategory (CategoryTheory.Center C.Obj) := MTC.Center.Rigid.rigidCenter
  letI : IsFusionCategory (CategoryTheory.Center C.Obj) :=
    MTC.Center.Induction.center_fusion_of_pivotal p
  exact degenerate_conclusions_of_relative_fusion_criterion C p hpositive
    (fun pZ A hA => hrelative (MTC.PropertyF.Reduction.bundledCenter C) pZ A hA) hF

end MTC.PropertyF.Pivotal
end
