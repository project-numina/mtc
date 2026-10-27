module
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.CentreCabling.TraceSaturation
public import PropertyF.Ground.CentreCabling.ProductCentralizer

/-! Relate the numerical centralizer to the actual symmetric core. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u
variable (C : Ground.BraidedFusionCategory.{v,u})
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- Actual centre labels centralizing both canonical images. -/
def symmetricCore : Set (Fin (rank (Integrate.bundledCenter C))) :=
  {y | (∀ X : C.Obj, Centre.Centralizes (simples (Integrate.bundledCenter C) y)
      ((CategoryTheory.Center.ofBraided C.Obj).obj X)) ∧
    (∀ X : C.Obj, Centre.Centralizes (simples (Integrate.bundledCenter C) y)
      ((Centre.negative C.Obj).obj X))}

/-- A core object lies over a transparent base object and is isomorphic to
its positive canonical image. -/
theorem symmetricCore_underlying_transparent
    (y : Fin (rank (Integrate.bundledCenter C))) (hy : y ∈ symmetricCore C) :
    Transparent (simples (Integrate.bundledCenter C) y).1 := by
  exact transparent_of_both_centralizers _
    ((Centre.centralizes_positive_image_iff _).mp hy.1)
    ((Centre.centralizes_negative_image_iff _).mp hy.2)

/-- Every core label is itself a product-retract label. -/
theorem symmetricCore_subset_productLabels
    (y : Fin (rank (Integrate.bundledCenter C))) (hy : y ∈ symmetricCore C) :
    y ∈ productLabels C := by
  apply (mem_productLabels C y).mpr
  let Y := simples (Integrate.bundledCenter C) y
  let e := Centre.positiveIsoOfCentralizesNegative Y hy.2
  exact Centre.productRetract_of_retract (Retract.ofIso e)
    (Centre.positive_productRetract Y.1)

/-- The positive spherical dimension of a core label equals the FP dimension
of its underlying transparent base object. -/
theorem symmetricCore_dimension_eq_underlying_fp
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (y : Fin (rank (Integrate.bundledCenter C))) :
    Modular.simpleDimension (Integrate.bundledCenter C) p y =
      (fpDimension C (simples (Integrate.bundledCenter C) y).1 : ℂ) := by
  rw [hdim]
  have heq := Integrate.center_forget_fpDimension C (simples (Integrate.bundledCenter C) y)
  change fpDimension C (simples (Integrate.bundledCenter C) y).1 = _ at heq
  rw [fpDimension_simple] at heq
  exact_mod_cast heq.symm

/-- Finite order of mixed monodromies turns the numerical centralizer of all
product labels into the actual symmetric core. -/
theorem numericalProductCentralizer_subset_symmetricCore
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hfinite : ∀ a ∈ productLabels C, ∀ y,
      IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) a) (simples (Integrate.bundledCenter C) y))))
    (y : Fin (rank (Integrate.bundledCenter C)))
    (hy : ∀ a ∈ productLabels C, Modular.categoricalS (Integrate.bundledCenter C) p a y =
      Modular.simpleDimension (Integrate.bundledCenter C) p a *
        Modular.simpleDimension (Integrate.bundledCenter C) p y) : y ∈ symmetricCore C := by
  let Z := Integrate.bundledCenter C
  have hc (X : CategoryTheory.Center C.Obj) (hX : Centre.ProductRetract X) :
      Centre.Centralizes (simples Z y) X := by
    apply Centre.centralizes_symm
    change Modular.doubleBraiding X (simples Z y) = 𝟙 _
    apply doubleBraiding_eq_one_of_simple_constituents Z Centre.ProductRetract
      (fun r hr => Centre.productRetract_of_retract r hr) X (simples Z y) hX
    intro a ha
    have ha' : a ∈ productLabels C := (mem_productLabels C a).mpr ha
    exact doubleBraiding_eq_one_of_sTest_of_finite_order Z p hdim a y (hfinite a ha' y) (hy a ha')
  exact ⟨fun X => hc _ (Centre.positive_productRetract X),
    fun X => hc _ (Centre.negative_productRetract X)⟩

/-- Under finite mixed monodromy, the actual symmetric core has the precise
S-double-centralizer test needed by the target reduction. -/
theorem productLabels_doubleCentralizer_of_finite_monodromy
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical) (hdet : (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0)
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hfinite : ∀ a ∈ productLabels C, ∀ y,
      IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) a) (simples (Integrate.bundledCenter C) y)))) :
    ∀ x, (∀ y ∈ symmetricCore C, Modular.categoricalS (Integrate.bundledCenter C) p y x =
      Modular.simpleDimension (Integrate.bundledCenter C) p y *
        Modular.simpleDimension (Integrate.bundledCenter C) p x) →
      Centre.ProductRetract (simples (Integrate.bundledCenter C) x) :=
  productLabels_doubleCentralizer C p hp hdet hdim (symmetricCore C)
    (numericalProductCentralizer_subset_symmetricCore C p hdim hfinite)

end PropertyF.Ground.CentreCabling
