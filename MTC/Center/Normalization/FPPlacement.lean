module
public import MTC.Center.Normalization.CommonCentralizer
public import MTC.Center.Braid.ImageCore
public import MTC.Center.Induction.PositivePivotal

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions MTC.PropertyF.Reduction

/-! # The FP column and the canonical centre core

Once the pivotal dimensions have been normalized on the Müger centre, every
simple in the actual common centralizer of the two canonical centre images has
its FP dimension. This is an actual-object prerequisite for placing the FP
column in the product-retract subcategory.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
  [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
local notation "𝒵ᶠ" => bundledCenter C

/-- Normalization on the actual transparent simples of the base transfers to
every simple in the common centralizer of the canonical centre images. -/
theorem symmetricCore_pivotalDimension_eq_fp
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, MTC.Center.Induction.PivotalCompatibleAt p pZ Z)
    (hnorm : ∀ i, MTC.Center.Transparent (simples C i) →
      pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    {y : Fin (rank 𝒵ᶠ)} (hy : y ∈ symmetricCore C) :
    pivotalDimension 𝒵ᶠ pZ (simples 𝒵ᶠ y) = (fpSimple 𝒵ᶠ y : ℂ) := by
  let Z : Center C.Obj := simples 𝒵ᶠ y
  let : Simple Z := simples_simple 𝒵ᶠ y
  let F := Center.ofBraided C.Obj
  let e := MTC.Center.positiveIsoOfCentralizesNegative Z hy.2
  let : F.PreservesMonomorphisms := ⟨fun f _ ↦
    (Center.forget C.Obj).mono_of_mono_map (show Mono f from inferInstance)⟩
  let : Simple (F.obj Z.1) := Simple.of_iso e.symm
  let : Simple Z.1 := Functor.simple_of_simple_obj F Z.1
  obtain ⟨i, ⟨s⟩⟩ := exists_simple_iso C Z.1
  have hztrans : MTC.Center.Transparent Z.1 := fun T ↦
    (positiveImages_centralize_iff _ _).mp (MTC.Center.centralizes_of_iso_left e.symm (hy.1 T))
  have hitrans : MTC.Center.Transparent (simples C i) :=
    transparent_of_retract (Retract.ofIso s.symm) hztrans
  rw [MTC.Center.Induction.center_pivotalDimension_forget (hcompat Z),
    pivotalDimension_iso p s, hnorm i hitrans, ← fpDimension_simple i,
    ← fpDimension_iso s, center_forget_fpDimension C, fpDimension_simple]


/-- An FP column is numerically central to the actual common canonical-image
centralizer once the base pivotal dimensions are normalized there. -/
theorem fpColumn_centralizes_symmetricCore
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, MTC.Center.Induction.PivotalCompatibleAt p pZ Z)
    (hnorm : ∀ i, MTC.Center.Transparent (simples C i) →
      pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    {x : Fin (rank 𝒵ᶠ)}
    (hcol : ∀ i, MTC.Modular.categoricalS 𝒵ᶠ pZ i x =
      pivotalDimension 𝒵ᶠ pZ (simples 𝒵ᶠ x) * (fpSimple 𝒵ᶠ i : ℂ)) :
    x ∈ MTC.Modular.sCentralizer 𝒵ᶠ pZ (symmetricCore C) := by
  intro y hy
  change MTC.Modular.categoricalS 𝒵ᶠ pZ y x = _
  rw [hcol y]
  change _ = pivotalDimension 𝒵ᶠ pZ (simples 𝒵ᶠ y) * pivotalDimension 𝒵ᶠ pZ (simples 𝒵ᶠ x)
  rw [symmetricCore_pivotalDimension_eq_fp C hcompat hnorm hy]
  ring

/-- Numerical centrality of the product labels implies actual common
canonical-image centrality as soon as the numerical S-test is known to imply
actual monodromy identity for simple canonical-image constituents. -/
theorem productNumericalCentralizer_subset_symmetricCore
    {pZ : PivotalStructure (C := Center C.Obj)}
    (hcriterion : ∀ a ∈ imageLabels C, ∀ y : Fin (rank 𝒵ᶠ),
      MTC.Modular.sCentralizes 𝒵ᶠ pZ a y →
      MTC.Modular.doubleBraiding (simples 𝒵ᶠ a) (simples 𝒵ᶠ y) = 𝟙 _) :
    MTC.Modular.sCentralizer 𝒵ᶠ pZ (↑(productLabels C) : Set _) ⊆ symmetricCore C := by
  intro y hy
  have h (X : Center C.Obj) (hX : CanonicalImageRetract X) :
      MTC.Center.Centralizes (simples 𝒵ᶠ y) X :=
    MTC.Center.centralizes_symm <| by
      obtain ⟨m, ⟨e⟩⟩ := simples_decompose 𝒵ᶠ X
      exact doubleBraiding_eq_one_of_constituents (simples 𝒵ᶠ) e CanonicalImageRetract
        (fun r hr ↦ canonicalImageRetract_of_retract r hr) hX fun a ha ↦
          hcriterion a ha y (hy a (imageLabels_subset_productLabels C ha))
  exact ⟨fun X ↦ h _ (Or.inl ⟨X, ⟨Retract.refl _⟩⟩),
    fun X ↦ h _ (Or.inr ⟨X, ⟨Retract.refl _⟩⟩)⟩

/-- The FP-column simple is a canonical product retract if Hermitian
orthogonality holds and numerical product centrality implies actual membership
in the common canonical-image centralizer. -/
theorem fpColumn_productRetract_of_numerical_centralizer
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, MTC.Center.Induction.PivotalCompatibleAt p pZ Z)
    (hnorm : ∀ i, MTC.Center.Transparent (simples C i) →
      pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (horth : ∀ x k : Fin (rank 𝒵ᶠ),
      (∑ y, star (MTC.Modular.categoricalS 𝒵ᶠ pZ y x) * MTC.Modular.categoricalS 𝒵ᶠ pZ y k) =
        if x = k then globalDimension 𝒵ᶠ else 0)
    (hcore : MTC.Modular.sCentralizer 𝒵ᶠ pZ (↑(productLabels C) : Set _) ⊆ symmetricCore C)
    {x : Fin (rank 𝒵ᶠ)}
    (hcol : ∀ i, MTC.Modular.categoricalS 𝒵ᶠ pZ i x =
      pivotalDimension 𝒵ᶠ pZ (simples 𝒵ᶠ x) * (fpSimple 𝒵ᶠ i : ℂ)) :
    MTC.Center.ProductRetract (simples 𝒵ᶠ x) :=
  (mem_productLabels C x).mp <|
    pivotal_doubleCentralizer_of_fusion_closed horth (productLabels_isFusionSubring C) hcore <|
      fpColumn_centralizes_symmetricCore C hcompat hnorm hcol

/-- Under the same explicit placement prerequisites, property F of the base
implies objectwise property F for the FP-column simple in its centre. -/
theorem fpColumn_objectPropertyF_of_numerical_centralizer
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, MTC.Center.Induction.PivotalCompatibleAt p pZ Z)
    (hnorm : ∀ i, MTC.Center.Transparent (simples C i) →
      pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (horth : ∀ x k : Fin (rank 𝒵ᶠ),
      (∑ y, star (MTC.Modular.categoricalS 𝒵ᶠ pZ y x) * MTC.Modular.categoricalS 𝒵ᶠ pZ y k) =
        if x = k then globalDimension 𝒵ᶠ else 0)
    (hcore : MTC.Modular.sCentralizer 𝒵ᶠ pZ (↑(productLabels C) : Set _) ⊆ symmetricCore C)
    {x : Fin (rank 𝒵ᶠ)}
    (hcol : ∀ i, MTC.Modular.categoricalS 𝒵ᶠ pZ i x =
      pivotalDimension 𝒵ᶠ pZ (simples 𝒵ᶠ x) * (fpSimple 𝒵ᶠ i : ℂ))
    (hF : HasPropertyF C.Obj) : ObjectPropertyF (simples 𝒵ᶠ x) :=
  MTC.Center.productRetract_propertyF
    (fpColumn_productRetract_of_numerical_centralizer C hcompat hnorm horth hcore hcol) hF

/-- The FP-column simple has property F when the numerical S-test is known to
imply actual centrality on simple canonical-image constituents. -/
theorem fpColumn_objectPropertyF_of_simple_criterion
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, MTC.Center.Induction.PivotalCompatibleAt p pZ Z)
    (hnorm : ∀ i, MTC.Center.Transparent (simples C i) →
      pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (horth : ∀ x k : Fin (rank 𝒵ᶠ),
      (∑ y, star (MTC.Modular.categoricalS 𝒵ᶠ pZ y x) * MTC.Modular.categoricalS 𝒵ᶠ pZ y k) =
        if x = k then globalDimension 𝒵ᶠ else 0)
    (hcriterion : ∀ a ∈ imageLabels C, ∀ y : Fin (rank 𝒵ᶠ),
      MTC.Modular.sCentralizes 𝒵ᶠ pZ a y →
      MTC.Modular.doubleBraiding (simples 𝒵ᶠ a) (simples 𝒵ᶠ y) = 𝟙 _)
    {x : Fin (rank 𝒵ᶠ)}
    (hcol : ∀ i, MTC.Modular.categoricalS 𝒵ᶠ pZ i x =
      pivotalDimension 𝒵ᶠ pZ (simples 𝒵ᶠ x) * (fpSimple 𝒵ᶠ i : ℂ))
    (hF : HasPropertyF C.Obj) : ObjectPropertyF (simples 𝒵ᶠ x) :=
  fpColumn_objectPropertyF_of_numerical_centralizer C hcompat hnorm horth
    (productNumericalCentralizer_subset_symmetricCore C hcriterion) hcol hF

end MTC.Center.Normalization
end
