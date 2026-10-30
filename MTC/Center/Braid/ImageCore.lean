module
public import MTC.Center.Braid.CentralityClosure
public import MTC.Center.Braid.TraceSaturation
public import MTC.Center.Braid.RegularSupport
public import MTC.Fusion.UnitPower
public import MTC.Center.Trace.TwistSign

/-!
# The symmetric core and canonical images

Product-retract labels are closed under tensor constituents and duals.
The two canonical images test membership in the actual symmetric core.
Centrality under product retracts identifies that core with its numerical
product centralizer, under the stated finite-monodromy hypotheses. We write
`𝒵 C` for the bundled centre of `C`.
-/

@[expose] public noncomputable section
open MTC.Modular (HasFPSimpleDimensions IsFPSpherical doubleBraiding sCentralizer)
open MTC.Dimensions
local notation "𝒵" => MTC.Integrate.bundledCenter
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CentreCabling
universe v u
variable (C : MTC.BraidedFusionCategory.{v,u})
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- The actual centre simple labels which are retracts of product images. -/
def productLabels : Finset (Fin (rank (𝒵 C))) := by
  classical
  exact Finset.univ.filter (fun i => Centre.ProductRetract (simples (𝒵 C) i))

/-- Product labels are exactly the labels of product retracts. -/
theorem mem_productLabels (i : Fin (rank (𝒵 C))) :
    i ∈ productLabels C ↔ Centre.ProductRetract (simples (𝒵 C) i) := by
  classical
  simp [productLabels]

/-- The unit label is a product label. -/
theorem unit_mem_productLabels : unitIndex (𝒵 C) ∈ productLabels C :=
  let ⟨e⟩ := unitIndex_iso (𝒵 C)
  (mem_productLabels C _).2 <|
    Centre.productRetract_of_retract (Retract.ofIso e) Centre.unit_productRetract

variable {i j : productLabels C}

/-- Product labels are closed under duals. -/
theorem dual_mem_productLabels : dualIndex (𝒵 C) i ∈ productLabels C :=
  let Z := 𝒵 C
  let X : CategoryTheory.Center C.Obj := simples Z i
  let e : (ᘁX) ≅ (Xᘁ) := leftDualIso HasLeftDual.exact
    (BraidedCategory.exactPairing_swap X (Xᘁ))
  let ⟨e'⟩ := dualIndex_iso (D := Z) i
  (mem_productLabels C _).2 <| Centre.productRetract_of_retract (Retract.ofIso (e'.symm ≪≫ e))
    (Centre.productRetract_rightDual C ((mem_productLabels C i).1 i.property))

/-- Every constituent label of two product labels is itself a product label. -/
theorem constituent_mem_productLabels
    (k : {k : Fin (rank (𝒵 C)) // 0 < fusionCoeff (𝒵 C) i j k}) : k.val ∈ productLabels C :=
  let ⟨r⟩ := MTC.fusionCoeff_retract k.property
  (mem_productLabels C k).2 <| Centre.productRetract_of_retract r <|
    Centre.productRetract_tensor ((mem_productLabels C i).1 i.2) ((mem_productLabels C j).1 j.2)

/-- The product-retract labels form a fusion subring. -/
theorem productLabels_isFusionSubring : IsFusionSubring (𝒵 C) (productLabels C) :=
  ⟨⟨(fun i hi ↦ dual_mem_productLabels C (i := ⟨i, hi⟩)),
    (fun i hi j hj k hk ↦ constituent_mem_productLabels C (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) ⟨k, hk⟩)⟩,
    unit_mem_productLabels C⟩

/-- The centre's product-retract labels satisfy the numerical double-centralizer
inclusion whenever the chosen core contains their numerical centralizer. -/
theorem productLabels_doubleCentralizer {p : PivotalStructure (C := (𝒵 C).Obj)}
    (hfp : IsFPSpherical (𝒵 C) p) (hdet : (Modular.categoricalS (𝒵 C) p).det ≠ 0)
    {core : Set (Fin (rank (𝒵 C)))}
    (hcore : sCentralizer (𝒵 C) p (↑(productLabels C) : Set _) ⊆ core) :
    ∀ x ∈ sCentralizer (𝒵 C) p core, Centre.ProductRetract (simples (𝒵 C) x) := fun x hx ↦
  (mem_productLabels C x).mp <|
    doubleCentralizer_of_fusion_closed hfp hdet (productLabels_isFusionSubring C) hcore hx


/-- Actual centre labels centralizing both canonical images. -/
def symmetricCore : Set (Fin (rank (𝒵 C))) :=
  {y | (∀ X : C.Obj, Centre.Centralizes (simples (𝒵 C) y)
      ((CategoryTheory.Center.ofBraided C.Obj).obj X)) ∧
    (∀ X : C.Obj, Centre.Centralizes (simples (𝒵 C) y)
      ((Centre.negative C.Obj).obj X))}

end MTC.CentreCabling

open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CentreCabling
universe v u
variable (C : MTC.BraidedFusionCategory.{v,u})
  [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]

section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- Retracts of either canonical image, without taking mixed products. -/
def CanonicalImageRetract (X : CategoryTheory.Center D) : Prop :=
  (∃ A : D, Nonempty (Retract X ((CategoryTheory.Center.ofBraided D).obj A))) ∨
  (∃ A : D, Nonempty (Retract X ((Centre.negative D).obj A)))

/-- Retracts of canonical-image retracts remain canonical-image retracts. -/
theorem canonicalImageRetract_of_retract {X Y : CategoryTheory.Center D}
    (r : Retract X Y) (h : CanonicalImageRetract Y) : CanonicalImageRetract X :=
  h.elim (fun ⟨A, ⟨s⟩⟩ ↦ Or.inl ⟨A, ⟨r.trans s⟩⟩)
    (fun ⟨A, ⟨s⟩⟩ ↦ Or.inr ⟨A, ⟨r.trans s⟩⟩)

/-- Every canonical-image retract is also a product retract. -/
theorem canonicalImageRetract_product {X : CategoryTheory.Center D}
    (h : CanonicalImageRetract X) : Centre.ProductRetract X :=
  h.elim (fun ⟨A, ⟨s⟩⟩ ↦ Centre.productRetract_of_retract s (Centre.positive_productRetract A))
    (fun ⟨A, ⟨s⟩⟩ ↦ Centre.productRetract_of_retract s (Centre.negative_productRetract A))
end

/-- Simple constituents of either canonical image. -/
def imageLabels : Set (Fin (rank (𝒵 C))) :=
  {a | CanonicalImageRetract (simples (𝒵 C) a)}

/-- Every canonical-image label is a product label. -/
theorem imageLabels_subset_productLabels : imageLabels C ⊆ (↑(productLabels C) : Set _) :=
  fun a ha ↦ (mem_productLabels C a).mpr (canonicalImageRetract_product ha)

variable {p : PivotalStructure (C := (𝒵 C).Obj)}

/-- Image monodromy is finite for labels passing the numerical centralizer test. -/
abbrev HasFiniteImageCentralizerMonodromy
    (p : PivotalStructure (C := (𝒵 C).Obj)) : Prop :=
  ∀ y ∈ sCentralizer (𝒵 C) p (imageLabels C),
      ∀ a ∈ imageLabels C, IsOfFinOrder (End.of (doubleBraiding
        (simples (𝒵 C) a) (simples (𝒵 C) y)))

variable (hp : p.IsSpherical)
  (hdet : (Modular.categoricalS (𝒵 C) p).det ≠ 0)
  (hdim : HasFPSimpleDimensions (𝒵 C) p)

variable (hfinite : HasFiniteImageCentralizerMonodromy C p)
  {y : Fin (rank (𝒵 C))} (hy : y ∈ sCentralizer (𝒵 C) p (imageLabels C))

include hdim hfinite hy in
/-- The numerical image centralizer centralizes every canonical-image retract. -/
theorem centralizes_imageRetract {X : CategoryTheory.Center C.Obj}
    (hX : CanonicalImageRetract X) : Centre.Centralizes (simples (𝒵 C) y) X :=
  Centre.centralizes_symm <| by
    obtain ⟨m, ⟨e⟩⟩ := simples_decompose (𝒵 C) X
    exact doubleBraiding_eq_one_of_constituents (simples (𝒵 C)) e CanonicalImageRetract
      (fun r hr ↦ canonicalImageRetract_of_retract r hr) hX fun a ha ↦
        doubleBraiding_eq_one_of_sTest_of_finite_order hdim (hfinite y hy a ha) (hy a ha)

include hdim hfinite hy in
/-- The S-test on both canonical images detects the actual core if the relevant
mixed monodromies have finite order. Only simple image constituents, and only
labels passing this S-test, are needed for the finite-order hypothesis. -/
theorem numericalImageCentralizer_subset_symmetricCore : y ∈ symmetricCore C :=
  let h (X : CategoryTheory.Center C.Obj) := centralizes_imageRetract C hdim hfinite hy (X := X)
  ⟨fun X ↦ h _ (Or.inl ⟨X, ⟨Retract.refl _⟩⟩),
    fun X ↦ h _ (Or.inr ⟨X, ⟨Retract.refl _⟩⟩)⟩

include hp hdet hdim in
/-- The precise actual-core double-centralizer conclusion under the reduced
finite-order condition for simple canonical-image constituents. -/
theorem productLabels_doubleCentralizer_of_image_monodromy
    (hfinite : HasFiniteImageCentralizerMonodromy C p) :
    ∀ x ∈ sCentralizer (𝒵 C) p (symmetricCore C),
      Centre.ProductRetract (simples (𝒵 C) x) :=
  productLabels_doubleCentralizer C ⟨hp, hdim⟩ hdet fun _ hy ↦
    numericalImageCentralizer_subset_symmetricCore C hdim hfinite fun a ha ↦
      hy a (imageLabels_subset_productLabels C ha)

end MTC.CentreCabling

namespace MTC.CentreCalculus
universe v u

/-- Every simple in the common centralizer of the two canonical images in
Mathlib's actual centre has integer categorical dimension in an FP-valued
spherical structure. -/
theorem actual_symmetricCore_integrality {C : BraidedFusionCategory.{v,u}}
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    {p : PivotalStructure (C := (𝒵 C).Obj)}
    (hfp : IsFPSpherical (𝒵 C) p) {y : CentreCabling.symmetricCore C} :
    ∃ z : ℤ, Modular.simpleDimension (𝒵 C) p y = z :=
  selfTransparent_simpleDimension_integer hfp
    (commonCentralizer_self (simples (𝒵 C) y) y.property.1 y.property.2)

end MTC.CentreCalculus
