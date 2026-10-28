module
public import PropertyF.Ground.CentreCabling.ProductCore

/-!
# The symmetric core and canonical images

The two canonical images test membership in the actual symmetric core.
Centrality under product retracts identifies that core with its numerical
product centralizer, under the stated finite-monodromy hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u
variable (C : Ground.BraidedFusionCategory.{v,u})
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- Retracts of either canonical image, without taking mixed products. -/
def CanonicalImageRetract (X : CategoryTheory.Center C.Obj) : Prop :=
  (∃ A : C.Obj, Nonempty (Retract X ((CategoryTheory.Center.ofBraided C.Obj).obj A))) ∨
  (∃ A : C.Obj, Nonempty (Retract X ((Centre.negative C.Obj).obj A)))

omit [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)] in
theorem canonicalImageRetract_of_retract {X Y : CategoryTheory.Center C.Obj}
    (r : Retract X Y) (h : CanonicalImageRetract C Y) : CanonicalImageRetract C X := by
  rcases h with ⟨A, ⟨s⟩⟩ | ⟨A, ⟨s⟩⟩
  · exact Or.inl ⟨A, ⟨r.trans s⟩⟩
  · exact Or.inr ⟨A, ⟨r.trans s⟩⟩

omit [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)] in
theorem canonicalImageRetract_product {X : CategoryTheory.Center C.Obj}
    (h : CanonicalImageRetract C X) : Centre.ProductRetract X := by
  rcases h with ⟨A, ⟨s⟩⟩ | ⟨A, ⟨s⟩⟩
  · exact Centre.productRetract_of_retract s (Centre.positive_productRetract A)
  · exact Centre.productRetract_of_retract s (Centre.negative_productRetract A)

/-- Simple constituents of either canonical image. -/
def imageLabels : Set (Fin (rank (Integrate.bundledCenter C))) :=
  {a | CanonicalImageRetract C (simples (Integrate.bundledCenter C) a)}

theorem imageLabels_subset_productLabels : imageLabels C ⊆ (↑(productLabels C) : Set _) :=
  fun a ha ↦ (mem_productLabels C a).mpr (canonicalImageRetract_product C ha)

variable (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))

/-- Image monodromy is finite for labels passing the numerical centralizer test. -/
abbrev HasFiniteImageCentralizerMonodromy : Prop :=
  ∀ y ∈ sCentralizer (Integrate.bundledCenter C) p (imageLabels C),
      ∀ a ∈ imageLabels C, IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) a) (simples (Integrate.bundledCenter C) y)))

variable (hp : p.IsSpherical)
  (hdet : (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0)
  (hdim : Modular.HasFPSimpleDimensions (Integrate.bundledCenter C) p)

include hdim in
/-- The S-test on both canonical images detects the actual core if the relevant
mixed monodromies have finite order. Only simple image constituents, and only
labels passing this S-test, are needed for the finite-order hypothesis. -/
theorem numericalImageCentralizer_subset_symmetricCore
    (hfinite : HasFiniteImageCentralizerMonodromy C p)
    (y : Fin (rank (Integrate.bundledCenter C)))
    (hy : y ∈ sCentralizer (Integrate.bundledCenter C) p (imageLabels C)) : y ∈ symmetricCore C := by
  let Z := Integrate.bundledCenter C
  have hc (X : CategoryTheory.Center C.Obj) (hX : CanonicalImageRetract C X) :
      Centre.Centralizes (simples Z y) X := by
    apply Centre.centralizes_symm
    change Modular.doubleBraiding X (simples Z y) = 𝟙 _
    apply doubleBraiding_eq_one_of_simple_constituents Z (CanonicalImageRetract C)
      (fun r hr => canonicalImageRetract_of_retract C r hr) hX
    intro a ha
    exact doubleBraiding_eq_one_of_sTest_of_finite_order Z p hdim
      (hfinite y hy a ha) (hy a ha)
  constructor
  · intro X
    exact hc _ (Or.inl ⟨X, ⟨Retract.refl _⟩⟩)
  · intro X
    exact hc _ (Or.inr ⟨X, ⟨Retract.refl _⟩⟩)

include hp hdet hdim in
/-- The precise actual-core double-centralizer conclusion under the reduced
finite-order condition for simple canonical-image constituents. -/
theorem productLabels_doubleCentralizer_of_image_monodromy
    (hfinite : HasFiniteImageCentralizerMonodromy C p) :
    ∀ x ∈ sCentralizer (Integrate.bundledCenter C) p (symmetricCore C),
      Centre.ProductRetract (simples (Integrate.bundledCenter C) x) := by
  apply productLabels_doubleCentralizer C p hp hdet hdim (symmetricCore C)
  intro y hy
  apply numericalImageCentralizer_subset_symmetricCore C p hdim hfinite y
  intro a ha
  exact hy a (imageLabels_subset_productLabels C ha)

end PropertyF.Ground.CentreCabling
