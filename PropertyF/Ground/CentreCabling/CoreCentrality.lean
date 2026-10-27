module
public import PropertyF.Ground.CentreCabling.ImageCore

/-! The actual core centralizes every product retract. -/

@[expose] public noncomputable section
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
