module
public import MTC.PropertyF.Pivotal.DegenerateRelative
public import MTC.PropertyF.Pivotal.NumericalReduction
public import MTC.PropertyF.Pivotal.CenterNondegenerate

/-! # Consequences of relative numerical-to-actual centrality

These adapters expose the relative categorical criterion as a premise. The
criterion itself is proved in `NondegeneracyRelative`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions
open MTC.Center.Braid
namespace MTC.PropertyF.Pivotal
set_option backward.isDefEq.respectTransparency false
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- The complete set of simple labels is a fusion subring. -/
theorem univ_isFusionSubring : IsFusionSubring C Finset.univ := by
  exact ⟨⟨(by simp), (by simp [IsFusionClosed])⟩, by simp⟩

/-- Centrality against all simple representatives implies actual transparency. -/
theorem transparent_of_simple_monodromy (k : Fin (rank C))
    (h : ∀ i, doubleBraiding (simples C i) (simples C k) = 𝟙 _) :
    MTC.Center.Transparent (simples C k) := by
  intro X
  have hx : doubleBraiding X (simples C k) = 𝟙 _ := by
    obtain ⟨m, ⟨e⟩⟩ := simples_decompose C X
    exact doubleBraiding_eq_one_of_constituents (simples C) e (fun _ => True)
      (fun _ _ => trivial) trivial (fun i _ => h i)
  change doubleBraiding (simples C k) X = 𝟙 _
  simpa [doubleBraiding, Category.assoc] using
    congrArg (fun f => (β_ X (simples C k)).inv ≫ f ≫ (β_ X (simples C k)).hom) hx

variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "Z" => MTC.PropertyF.Reduction.bundledCenter C

/-- The two exact centre interfaces needed for the degenerate theorem follow
from the relative centrality criterion for actual centre fusion subrings. -/
theorem degenerate_conclusions_of_relative_fusion_criterion
    (p : PivotalStructure (C := C.Obj))
    (hpositive : PositiveOnTransparentAdjoint C p)
    (hrelative : ∀ (pZ : PivotalStructure (C := (MTC.PropertyF.Reduction.bundledCenter C).Obj))
      (A : Finset (Fin (rank Z))), IsFusionSubring Z A → ∀ y : Fin (rank Z),
      (∀ a ∈ A, sCentralizes Z pZ a y) →
      ∀ a ∈ A, doubleBraiding (simples Z a) (simples Z y) = 𝟙 _)
    (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
      WeaklyIntegral (globalFPDimension C) := by
  apply degenerate_conclusions_of_relative_center_criterion C p hpositive
  · intro pZ
    apply categoricalS_invertible_of_nondegenerate_of_numerical_transparency Z pZ
      (isNondegenerate_center C)
    intro k hk
    apply transparent_of_simple_monodromy Z k
    intro i
    exact hrelative pZ Finset.univ (univ_isFusionSubring Z) k
      (fun a _ => hk a) i (Finset.mem_univ i)
  · intro pZ
    exact hrelative pZ (productLabels C) (productLabels_isFusionSubring C)
  · exact hF

end MTC.PropertyF.Pivotal
end
