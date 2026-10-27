module
public import PropertyF.Ground.Integrate.CenterCentralizers
public import PropertyF.Ground.Centre.ProductClosure

/-! Transfer finite braid images from actual centre product retracts. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory
namespace PropertyF.Ground
universe v u v' u'

/-- A faithful braided functor reflects the finite image of a product retract. -/
theorem propertyF_of_center_productRetract (C : BraidedFusionCategory.{v,u})
    (Z : BraidedFusionCategory.{v',u'}) (F : Z.Obj ⥤ CategoryTheory.Center C.Obj)
    [F.Braided] [F.Faithful] (hF : HasPropertyF C.Obj)
    (X : Z.Obj) (hX : Centre.ProductRetract (F.obj X)) : ObjectPropertyF X := by
  have hf := Centre.productRetract_propertyF hX hF
  intro n
  letI : Finite (braidImage (F.obj X) n) := hf n
  exact Finite.of_injective (Modular.braidImageFunctorIso F X n)
    (Modular.braidImageFunctorIso F X n).injective

/-- Replace the generated-label finite-image premise by actual product
retracts in Mathlib’s centre. The centre and centralizer facts remain explicit
unproved premises of this reduction. -/
theorem target_of_center_product_retracts
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,max u v}) (p : Dimensions.PivotalStructure (C := Z.Obj))
        (F : Z.Obj ⥤ CategoryTheory.Center C.Obj),
        Nonempty F.Braided ∧ F.Faithful ∧
      ∃ (core generated : Set (Fin (rank Z))),
        p.IsSpherical ∧
        (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z) ∧
        (∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
          Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated) ∧
        (∀ y ∈ generated, Centre.ProductRetract (F.obj (simples Z y)))) :
    TargetStatement.{v,u} := by
  apply target_of_center_centralizers
  intro C hPU hF σ
  obtain ⟨Z, p, F, hB, hfaithful, core, generated, hp, hdim, hdet, hglobal,
    hIntegral, hDouble, hProduct⟩ := hCenter C hPU hF σ
  letI : F.Braided := hB.some
  letI : F.Faithful := hfaithful
  refine ⟨Z, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, ?_⟩
  intro y hy
  exact propertyF_of_center_productRetract C Z F hF (simples Z y) (hProduct y hy)

end PropertyF.Ground
