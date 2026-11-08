module
public import MTC.Center.Normalization.FPPlacement

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions
open MTC.PropertyF.Reduction MTC.Modular

/-! # Relative numerical-to-actual centre centralizer adapter

The missing relative numerical-to-actual theorem is an explicit hypothesis.
This file checks how its product-label instance enters the centre reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
  [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
local notation "Z" => bundledCenter C

/-- A relative numerical-to-actual centrality theorem for the fusion subring
of product labels supplies exactly the common-centralizer containment needed
in the centre reduction. No pairwise numerical criterion is assumed. -/
theorem productNumericalCentralizer_subset_symmetricCore_of_relative
    {pZ : PivotalStructure (C := Center C.Obj)}
    (hrelative : ∀ y : Fin (rank Z),
      (∀ a ∈ productLabels C, sCentralizes Z pZ a y) →
      ∀ a ∈ productLabels C, doubleBraiding (simples Z a) (simples Z y) = 𝟙 _) :
    sCentralizer Z pZ (↑(productLabels C) : Set _) ⊆ symmetricCore C := by
  intro y hy
  have hy' : ∀ a ∈ productLabels C, sCentralizes Z pZ a y := fun a ha => hy a ha
  have h (X : Center C.Obj) (hX : CanonicalImageRetract X) :
      MTC.Center.Centralizes (simples Z y) X :=
    MTC.Center.centralizes_symm <| by
      obtain ⟨m, ⟨e⟩⟩ := simples_decompose Z X
      exact doubleBraiding_eq_one_of_constituents (simples Z) e CanonicalImageRetract
        (fun r hr ↦ canonicalImageRetract_of_retract r hr) hX fun a ha ↦
          hrelative y hy' a (imageLabels_subset_productLabels C ha)
  exact ⟨fun X ↦ h _ (Or.inl ⟨X, ⟨Retract.refl _⟩⟩),
    fun X ↦ h _ (Or.inr ⟨X, ⟨Retract.refl _⟩⟩)⟩

/-- The generic relative numerical-to-actual criterion for fusion subrings
supplies the product-centralizer containment by applying it to the actual
fusion subring of product labels. -/
theorem productNumericalCentralizer_subset_symmetricCore_of_fusionSubring_criterion
    {pZ : PivotalStructure (C := Center C.Obj)}
    (hrelative : ∀ (A : Finset (Fin (rank Z))), IsFusionSubring Z A →
      ∀ y : Fin (rank Z), (∀ a ∈ A, sCentralizes Z pZ a y) →
      ∀ a ∈ A, doubleBraiding (simples Z a) (simples Z y) = 𝟙 _) :
    sCentralizer Z pZ (↑(productLabels C) : Set _) ⊆ symmetricCore C :=
  productNumericalCentralizer_subset_symmetricCore_of_relative C
    (hrelative (productLabels C) (productLabels_isFusionSubring C))

end MTC.Center.Normalization
end
