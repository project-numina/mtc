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

theorem canonicalImageRetract_of_retract {X Y : CategoryTheory.Center C.Obj}
    (r : Retract X Y) (h : CanonicalImageRetract C Y) : CanonicalImageRetract C X := by
  rcases h with ⟨A, ⟨s⟩⟩ | ⟨A, ⟨s⟩⟩
  · exact Or.inl ⟨A, ⟨r.trans s⟩⟩
  · exact Or.inr ⟨A, ⟨r.trans s⟩⟩

theorem canonicalImageRetract_product {X : CategoryTheory.Center C.Obj}
    (h : CanonicalImageRetract C X) : Centre.ProductRetract X := by
  rcases h with ⟨A, ⟨s⟩⟩ | ⟨A, ⟨s⟩⟩
  · exact Centre.productRetract_of_retract s (Centre.positive_productRetract A)
  · exact Centre.productRetract_of_retract s (Centre.negative_productRetract A)

/-- A retract of the positive embedding is canonically isomorphic to the
positive image of its underlying object. -/
def positiveIsoOfImageRetract (Y : CategoryTheory.Center C.Obj) (A : C.Obj)
    (r : Retract Y ((CategoryTheory.Center.ofBraided C.Obj).obj A)) :
    Y ≅ (CategoryTheory.Center.ofBraided C.Obj).obj Y.1 := by
  apply Centre.positiveIsoOfCentralizesNegative
  intro X
  change Modular.doubleBraiding Y ((Centre.negative C.Obj).obj X) = 𝟙 _
  apply doubleBraiding_eq_one_of_retract r
  exact Centre.positive_negative_centralize A X

/-- The analogous statement for the negative embedding. -/
def negativeIsoOfImageRetract (Y : CategoryTheory.Center C.Obj) (A : C.Obj)
    (r : Retract Y ((Centre.negative C.Obj).obj A)) :
    Y ≅ (Centre.negative C.Obj).obj Y.1 := by
  apply Centre.negativeIsoOfCentralizesPositive
  intro X
  change Modular.doubleBraiding Y ((CategoryTheory.Center.ofBraided C.Obj).obj X) = 𝟙 _
  apply doubleBraiding_eq_one_of_retract r
  exact Centre.centralizes_symm (Centre.positive_negative_centralize X A)

/-- Simple constituents of either canonical image. -/
def imageLabels : Set (Fin (rank (Integrate.bundledCenter C))) :=
  {a | CanonicalImageRetract C (simples (Integrate.bundledCenter C) a)}

theorem imageLabels_subset_productLabels : imageLabels C ⊆ (↑(productLabels C) : Set _) := by
  intro a ha
  exact (mem_productLabels C a).mpr (canonicalImageRetract_product C ha)

/-- Each simple image label has a simple underlying base object. -/
theorem imageLabel_underlying_simple
    (a : Fin (rank (Integrate.bundledCenter C))) (ha : a ∈ imageLabels C) :
    Simple (simples (Integrate.bundledCenter C) a).1 := by
  let Y : CategoryTheory.Center C.Obj := simples (Integrate.bundledCenter C) a
  letI : Simple Y := simples_simple (Integrate.bundledCenter C) a
  letI : (CategoryTheory.Center.ofBraided C.Obj).PreservesMonomorphisms := {
    preserves := fun f => by
      intro _
      apply (CategoryTheory.Center.forget C.Obj).mono_of_mono_map
      change Mono f
      infer_instance }
  letI : (Centre.negative C.Obj).PreservesMonomorphisms := {
    preserves := fun f => by
      intro _
      apply (CategoryTheory.Center.forget C.Obj).mono_of_mono_map
      change Mono f
      infer_instance }
  rcases ha with ⟨A, ⟨r⟩⟩ | ⟨A, ⟨r⟩⟩
  · let e := positiveIsoOfImageRetract C Y A r
    letI : Simple ((CategoryTheory.Center.ofBraided C.Obj).obj Y.1) := Simple.of_iso e.symm
    exact Functor.simple_of_simple_obj (CategoryTheory.Center.ofBraided C.Obj) Y.1
  · let e := negativeIsoOfImageRetract C Y A r
    letI : Simple ((Centre.negative C.Obj).obj Y.1) := Simple.of_iso e.symm
    exact Functor.simple_of_simple_obj (Centre.negative C.Obj) Y.1

/-- A symmetric-core label has a simple underlying transparent base object. -/
theorem symmetricCore_underlying_simple
    (a : Fin (rank (Integrate.bundledCenter C))) (ha : a ∈ symmetricCore C) :
    Simple (simples (Integrate.bundledCenter C) a).1 := by
  apply imageLabel_underlying_simple C a
  left
  let Y : CategoryTheory.Center C.Obj := simples (Integrate.bundledCenter C) a
  exact ⟨Y.1, ⟨Retract.ofIso (Centre.positiveIsoOfCentralizesNegative Y ha.2)⟩⟩

/-- The S-test on both canonical images detects the actual core if the relevant
mixed monodromies have finite order. Only simple image constituents, and only
labels passing this S-test, are needed for the finite-order hypothesis. -/
theorem numericalImageCentralizer_subset_symmetricCore
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hfinite : ∀ y, (∀ a ∈ imageLabels C,
      Modular.categoricalS (Integrate.bundledCenter C) p a y =
        Modular.simpleDimension (Integrate.bundledCenter C) p a *
          Modular.simpleDimension (Integrate.bundledCenter C) p y) →
      ∀ a ∈ imageLabels C, IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) a) (simples (Integrate.bundledCenter C) y))))
    (y : Fin (rank (Integrate.bundledCenter C)))
    (hy : ∀ a ∈ imageLabels C, Modular.categoricalS (Integrate.bundledCenter C) p a y =
      Modular.simpleDimension (Integrate.bundledCenter C) p a *
        Modular.simpleDimension (Integrate.bundledCenter C) p y) : y ∈ symmetricCore C := by
  let Z := Integrate.bundledCenter C
  have hc (X : CategoryTheory.Center C.Obj) (hX : CanonicalImageRetract C X) :
      Centre.Centralizes (simples Z y) X := by
    apply Centre.centralizes_symm
    change Modular.doubleBraiding X (simples Z y) = 𝟙 _
    apply doubleBraiding_eq_one_of_simple_constituents Z (CanonicalImageRetract C)
      (fun r hr => canonicalImageRetract_of_retract C r hr) X (simples Z y) hX
    intro a ha
    exact doubleBraiding_eq_one_of_sTest_of_finite_order Z p hdim a y
      (hfinite y hy a ha) (hy a ha)
  constructor
  · intro X
    exact hc _ (Or.inl ⟨X, ⟨Retract.refl _⟩⟩)
  · intro X
    exact hc _ (Or.inr ⟨X, ⟨Retract.refl _⟩⟩)

/-- The precise actual-core double-centralizer conclusion under the reduced
finite-order condition for simple canonical-image constituents. -/
theorem productLabels_doubleCentralizer_of_image_monodromy
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical) (hdet : (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0)
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hfinite : ∀ y, (∀ a ∈ imageLabels C,
      Modular.categoricalS (Integrate.bundledCenter C) p a y =
        Modular.simpleDimension (Integrate.bundledCenter C) p a *
          Modular.simpleDimension (Integrate.bundledCenter C) p y) →
      ∀ a ∈ imageLabels C, IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) a) (simples (Integrate.bundledCenter C) y)))) :
    ∀ x, (∀ y ∈ symmetricCore C, Modular.categoricalS (Integrate.bundledCenter C) p y x =
      Modular.simpleDimension (Integrate.bundledCenter C) p y *
        Modular.simpleDimension (Integrate.bundledCenter C) p x) →
      Centre.ProductRetract (simples (Integrate.bundledCenter C) x) := by
  apply productLabels_doubleCentralizer C p hp hdet hdim (symmetricCore C)
  intro y hy
  apply numericalImageCentralizer_subset_symmetricCore C p hdim hfinite y
  intro a ha
  exact hy a (imageLabels_subset_productLabels C ha)

end PropertyF.Ground.CentreCabling

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u

/-- Centrality is preserved when tensoring the second strand. -/
theorem doubleBraiding_eq_one_tensor_right
    {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (Z X Y : D) (hX : Modular.doubleBraiding Z X = 𝟙 _)
    (hY : Modular.doubleBraiding Z Y = 𝟙 _) :
    Modular.doubleBraiding Z (X ⊗ Y) = 𝟙 _ := by
  have hβ : (β_ X Z).hom = (β_ Z X).inv := by
    apply (cancel_epi (β_ Z X).hom).mp
    simpa [Modular.doubleBraiding] using hX
  have hf := Modular.doubleBraiding_tensor_factorization Z X Y
  rw [hY] at hf
  simp only [whiskerLeft_id, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id_assoc, hβ, ← comp_whiskerRight, Iso.hom_inv_id,
    id_whiskerRight] at hf
  apply (cancel_epi (α_ Z X Y).hom).mp
  apply (cancel_mono (α_ Z X Y).inv).mp
  simpa using hf

/-- Every actual symmetric-core object centralizes all product retracts. -/
theorem symmetricCore_centralizes_productRetract
    (C : Ground.BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (y : Fin (rank (Integrate.bundledCenter C))) (hy : y ∈ symmetricCore C)
    (W : CategoryTheory.Center C.Obj) (hW : Centre.ProductRetract W) :
    Centre.Centralizes (simples (Integrate.bundledCenter C) y) W := by
  let Z := simples (Integrate.bundledCenter C) y
  obtain ⟨X, Y, ⟨r⟩⟩ := hW
  have hprod : Centre.Centralizes Z (Centre.productFunctor.obj (X,Y)) := by
    change Modular.doubleBraiding Z
      ((CategoryTheory.Center.ofBraided C.Obj).obj X ⊗ (Centre.negative C.Obj).obj Y) = 𝟙 _
    exact doubleBraiding_eq_one_tensor_right Z _ _ (hy.1 X) (hy.2 Y)
  apply Centre.centralizes_symm
  change Modular.doubleBraiding W Z = 𝟙 _
  apply doubleBraiding_eq_one_of_retract r Z
  exact Centre.centralizes_symm hprod

/-- Actual core labels satisfy the numerical S-test against every product
retract label without any finite-order hypothesis. -/
theorem symmetricCore_numericalProductCentralizer
    (C : Ground.BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (y : Fin (rank (Integrate.bundledCenter C))) (hy : y ∈ symmetricCore C) :
    ∀ a ∈ productLabels C, Modular.categoricalS (Integrate.bundledCenter C) p a y =
      Modular.simpleDimension (Integrate.bundledCenter C) p a *
        Modular.simpleDimension (Integrate.bundledCenter C) p y := by
  intro a ha
  have h := symmetricCore_centralizes_productRetract C y hy _ ((mem_productLabels C a).mp ha)
  have hh := Centre.centralizes_symm h
  exact categoricalS_eq_of_doubleBraiding (Integrate.bundledCenter C) p a y hh

/-- Under the reduced finite-order hypothesis, the actual symmetric core is
exactly the numerical S-centralizer of the product-retract labels. -/
theorem symmetricCore_iff_numericalProductCentralizer
    (C : Ground.BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hfinite : ∀ y, (∀ a ∈ imageLabels C,
      Modular.categoricalS (Integrate.bundledCenter C) p a y =
        Modular.simpleDimension (Integrate.bundledCenter C) p a *
          Modular.simpleDimension (Integrate.bundledCenter C) p y) →
      ∀ a ∈ imageLabels C, IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) a) (simples (Integrate.bundledCenter C) y))))
    (y : Fin (rank (Integrate.bundledCenter C))) :
    y ∈ symmetricCore C ↔ ∀ a ∈ productLabels C,
      Modular.categoricalS (Integrate.bundledCenter C) p a y =
        Modular.simpleDimension (Integrate.bundledCenter C) p a *
          Modular.simpleDimension (Integrate.bundledCenter C) p y := by
  constructor
  · exact symmetricCore_numericalProductCentralizer C p y
  · intro h
    apply numericalImageCentralizer_subset_symmetricCore C p hdim hfinite y
    intro a ha
    exact h a (imageLabels_subset_productLabels C ha)

end PropertyF.Ground.CentreCabling
