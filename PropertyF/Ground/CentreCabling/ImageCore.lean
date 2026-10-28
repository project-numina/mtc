module
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.CentreCabling.TraceSaturation
public import PropertyF.Ground.CentreCabling.RegularSupport
public import PropertyF.Ground.Fusion.UnitPower
public import PropertyF.Ground.CentreCalculus.TwistSign

/-!
# The symmetric core and canonical images

Product-retract labels are closed under tensor constituents and duals.
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

/-- The actual centre simple labels which are retracts of product images. -/
def productLabels : Finset (Fin (rank (Integrate.bundledCenter C))) := by
  classical
  exact Finset.univ.filter (fun i => Centre.ProductRetract (simples (Integrate.bundledCenter C) i))

theorem mem_productLabels (i : Fin (rank (Integrate.bundledCenter C))) :
    i ∈ productLabels C ↔ Centre.ProductRetract (simples (Integrate.bundledCenter C) i) := by
  classical
  simp [productLabels]

theorem unit_mem_productLabels : unitIndex (Integrate.bundledCenter C) ∈ productLabels C :=
  let ⟨e⟩ := unitIndex_iso (Integrate.bundledCenter C)
  (mem_productLabels C _).2 <|
    Centre.productRetract_of_retract (Retract.ofIso e) Centre.unit_productRetract

theorem dual_mem_productLabels {i : Fin (rank (Integrate.bundledCenter C))}
    (hi : i ∈ productLabels C) : dualIndex (Integrate.bundledCenter C) i ∈ productLabels C :=
  let Z := Integrate.bundledCenter C
  let X : CategoryTheory.Center C.Obj := simples Z i
  let e : (ᘁX) ≅ (Xᘁ) := leftDualIso HasLeftDual.exact
    (BraidedCategory.exactPairing_swap X (Xᘁ))
  let ⟨e'⟩ := dualIndex_iso Z i
  (mem_productLabels C _).2 <| Centre.productRetract_of_retract (Retract.ofIso (e'.symm ≪≫ e))
    (Centre.productRetract_rightDual C ((mem_productLabels C i).1 hi))

theorem constituent_mem_productLabels
    {i j k : Fin (rank (Integrate.bundledCenter C))}
    (hi : i ∈ productLabels C) (hj : j ∈ productLabels C)
    (hk : 0 < fusionCoeff (Integrate.bundledCenter C) i j k) : k ∈ productLabels C :=
  let ⟨r⟩ := Ground.fusionCoeff_retract (Integrate.bundledCenter C) hk
  (mem_productLabels C k).2 <| Centre.productRetract_of_retract r <|
    Centre.productRetract_tensor ((mem_productLabels C i).1 hi) ((mem_productLabels C j).1 hj)

/-- The centre's product-retract labels satisfy the numerical double-centralizer
inclusion whenever the chosen core contains their numerical centralizer. -/
theorem productLabels_doubleCentralizer
    {p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj)}
    (hp : p.IsSpherical) (hdet : (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0)
    (hdim : Modular.HasFPSimpleDimensions (Integrate.bundledCenter C) p)
    {core : Set (Fin (rank (Integrate.bundledCenter C)))}
    (hcore : sCentralizer (Integrate.bundledCenter C) p (↑(productLabels C) : Set _) ⊆ core) :
    ∀ x ∈ sCentralizer (Integrate.bundledCenter C) p core,
      Centre.ProductRetract (simples (Integrate.bundledCenter C) x) := fun x hx ↦
  (mem_productLabels C x).mp <|
    doubleCentralizer_of_fusion_closed hp hdet hdim
      (unit_mem_productLabels C)
      ⟨(fun _ hi ↦ dual_mem_productLabels C hi),
        (fun _ hi _ hj _ hk ↦ constituent_mem_productLabels C hi hj hk)⟩ hcore hx


/-- Actual centre labels centralizing both canonical images. -/
def symmetricCore : Set (Fin (rank (Integrate.bundledCenter C))) :=
  {y | (∀ X : C.Obj, Centre.Centralizes (simples (Integrate.bundledCenter C) y)
      ((CategoryTheory.Center.ofBraided C.Obj).obj X)) ∧
    (∀ X : C.Obj, Centre.Centralizes (simples (Integrate.bundledCenter C) y)
      ((Centre.negative C.Obj).obj X))}

end PropertyF.Ground.CentreCabling

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
    (r : Retract X Y) (h : CanonicalImageRetract C Y) : CanonicalImageRetract C X :=
  h.elim (fun ⟨A, ⟨s⟩⟩ ↦ Or.inl ⟨A, ⟨r.trans s⟩⟩)
    (fun ⟨A, ⟨s⟩⟩ ↦ Or.inr ⟨A, ⟨r.trans s⟩⟩)

omit [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)] in
theorem canonicalImageRetract_product {X : CategoryTheory.Center C.Obj}
    (h : CanonicalImageRetract C X) : Centre.ProductRetract X :=
  h.elim (fun ⟨A, ⟨s⟩⟩ ↦ Centre.productRetract_of_retract s (Centre.positive_productRetract A))
    (fun ⟨A, ⟨s⟩⟩ ↦ Centre.productRetract_of_retract s (Centre.negative_productRetract A))

/-- Simple constituents of either canonical image. -/
def imageLabels : Set (Fin (rank (Integrate.bundledCenter C))) :=
  {a | CanonicalImageRetract C (simples (Integrate.bundledCenter C) a)}

theorem imageLabels_subset_productLabels : imageLabels C ⊆ (↑(productLabels C) : Set _) :=
  fun a ha ↦ (mem_productLabels C a).mpr (canonicalImageRetract_product C ha)

variable {p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj)}

/-- Image monodromy is finite for labels passing the numerical centralizer test. -/
abbrev HasFiniteImageCentralizerMonodromy
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj)) : Prop :=
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
    {y : Fin (rank (Integrate.bundledCenter C))}
    (hy : y ∈ sCentralizer (Integrate.bundledCenter C) p (imageLabels C)) : y ∈ symmetricCore C := by
  let Z := Integrate.bundledCenter C
  have hc (X : CategoryTheory.Center C.Obj) (hX : CanonicalImageRetract C X) :
      Centre.Centralizes (simples Z y) X := by
    apply Centre.centralizes_symm
    change Modular.doubleBraiding X (simples Z y) = 𝟙 _
    apply doubleBraiding_eq_one_of_simple_constituents Z (CanonicalImageRetract C)
      (fun r hr => canonicalImageRetract_of_retract C r hr) hX
    intro a ha
    exact doubleBraiding_eq_one_of_sTest_of_finite_order hdim
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
      Centre.ProductRetract (simples (Integrate.bundledCenter C) x) :=
  productLabels_doubleCentralizer C hp hdet hdim fun _ hy ↦
    numericalImageCentralizer_subset_symmetricCore C hdim hfinite fun a ha ↦
      hy a (imageLabels_subset_productLabels C ha)

end PropertyF.Ground.CentreCabling

namespace PropertyF.Ground.CentreCalculus
universe v u

/-- Every simple in the common centralizer of the two canonical images in
Mathlib's actual centre has integer categorical dimension in an FP-valued
spherical structure. -/
theorem actual_symmetricCore_integrality {C : BraidedFusionCategory.{v,u}}
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    {p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj)}
    (hfp : IsFPSpherical (Integrate.bundledCenter C) p) :
    ∀ y ∈ CentreCabling.symmetricCore C,
      ∃ z : ℤ, Modular.simpleDimension (Integrate.bundledCenter C) p y = z :=
  fun y hy ↦ selfTransparent_simpleDimension_integer hfp
    (commonCentralizer_self (simples (Integrate.bundledCenter C) y) hy.1 hy.2)

end PropertyF.Ground.CentreCalculus
