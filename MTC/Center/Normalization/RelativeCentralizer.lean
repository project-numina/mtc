module
public import MTC.Center.Normalization.FPPlacement
public import MTC.PropertyF.Pivotal.Nondegeneracy

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions
open MTC.PropertyF.Reduction MTC.Modular

/-! # Relative numerical-to-actual centre centralizer adapter

The relative numerical-to-actual criterion is an explicit hypothesis here.
This file shows how its product-label instance enters the centre reduction.
`MTC.PropertyF.Pivotal.relative_fusionSubring_numerical_centrality` later
proves the criterion for arbitrary fusion subrings.
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

/-- The same relative criterion implies S invertibility whenever the unit is
the only transparent simple object. -/
theorem categoricalS_det_ne_zero_of_relative_and_trivial_transparency
    (D : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := D.Obj))
    (htrivial : ∀ k, MTC.Center.Transparent (simples D k) → k = unitIndex D)
    (hrelative : ∀ (A : Finset (Fin (rank D))), IsFusionSubring D A →
      ∀ y : Fin (rank D), (∀ a ∈ A, sCentralizes D p a y) →
      ∀ a ∈ A, doubleBraiding (simples D a) (simples D y) = 𝟙 _) :
    (categoricalS D p).det ≠ 0 := by
  classical
  apply MTC.PropertyF.Pivotal.categoricalS_det_ne_zero_of_trivial_S_centralizer D p
  intro k hs
  apply htrivial k
  have hA : IsFusionSubring D Finset.univ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj k hk
      exact Finset.mem_univ _
    · exact Finset.mem_univ _
  have hmono (i : Fin (rank D)) : doubleBraiding (simples D i) (simples D k) = 𝟙 _ :=
    hrelative Finset.univ hA k (fun i _ => hs i) i (Finset.mem_univ i)
  intro X
  have hx : doubleBraiding X (simples D k) = 𝟙 _ := by
    obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
    apply doubleBraiding_eq_one_of_constituents (simples D) e (fun _ => True)
      (fun _ _ => trivial) trivial
    intro i _
    exact hmono i
  change doubleBraiding (simples D k) X = 𝟙 _
  simpa [doubleBraiding, Category.assoc] using
    congrArg (fun f => (β_ X (simples D k)).inv ≫ f ≫ (β_ X (simples D k)).hom) hx

set_option backward.isDefEq.respectTransparency false in
/-- A relative numerical-to-actual centrality theorem gives invertibility of
the categorical S matrix of the actual Drinfeld centre. -/
theorem center_categoricalS_det_ne_zero_of_relative
    (pZ : PivotalStructure (C := Center C.Obj))
    (hrelative : ∀ (A : Finset (Fin (rank Z))), IsFusionSubring Z A →
      ∀ y : Fin (rank Z), (∀ a ∈ A, sCentralizes Z pZ a y) →
      ∀ a ∈ A, doubleBraiding (simples Z a) (simples Z y) = 𝟙 _) :
    (categoricalS Z pZ).det ≠ 0 := by
  apply categoricalS_det_ne_zero_of_relative_and_trivial_transparency Z pZ ?_ hrelative
  intro i hi
  let : Simple (simples Z i) := simples_simple Z i
  have ht : ∀ W : Center C.Obj, MTC.Center.Centralizes (simples Z i) W := hi
  obtain ⟨e⟩ := MTC.Center.Induction.center_transparent_simple_iso_unit (C := C) ht
  apply simples_injective Z
  exact ⟨e ≪≫ (unitIndex_iso Z).some.symm⟩

end MTC.Center.Normalization
end
