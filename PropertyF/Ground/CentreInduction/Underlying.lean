module
public import PropertyF.Ground.Fusion.FunctorDimension

/-! The underlying object of the induction construction for the Drinfeld centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The finite direct sum underlying the induction object. No half-braiding is
claimed here. -/
def underlying (C : BraidedFusionCategory.{v,u}) (X : C.Obj) : C.Obj :=
  ⨁ (fun i : Fin (rank C) => (simples C i ⊗ X) ⊗ (simples C i)ᘁ)

/-- The underlying induction object has FP dimension `FPdim(C) * FPdim(X)`.
This calculation does not require the centre to be fusion or the existence of
its induction half-braiding. -/
theorem fpDimension_underlying (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    fpDimension C (underlying C X) = globalFPDimension C * fpDimension C X := by
  classical
  rw [underlying, fpDimension_biproduct]
  simp_rw [fpDimension_tensor, fpDimension_rightDual, fpDimension_simple]
  rw [globalFPDimension, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The induction sum is functorial in its middle factor. Its centre lift is
constructed from the induction half-braiding. -/
def underlyingFunctor (C : BraidedFusionCategory.{v,u}) : C.Obj ⥤ C.Obj where
  obj := underlying C
  map {X Y} f := CategoryTheory.Limits.biproduct.map
    (fun i : Fin (rank C) => (simples C i ◁ f) ▷ (simples C i)ᘁ)
  map_id X := by
    apply CategoryTheory.Limits.biproduct.hom_ext'
    intro i
    apply CategoryTheory.Limits.biproduct.hom_ext
    intro j
    simp [underlying]
  map_comp f g := by
    apply CategoryTheory.Limits.biproduct.hom_ext'
    intro i
    apply CategoryTheory.Limits.biproduct.hom_ext
    intro j
    simp [underlying, Category.assoc, CategoryTheory.MonoidalCategory.whiskerLeft_comp,
      CategoryTheory.MonoidalCategory.comp_whiskerRight]

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
instance underlyingFunctor_additive (C : BraidedFusionCategory.{v,u}) :
    (underlyingFunctor C).Additive where
  map_add := by
    intro X Y f g
    apply CategoryTheory.Limits.biproduct.hom_ext'
    intro i
    apply CategoryTheory.Limits.biproduct.hom_ext
    intro j
    simp [underlyingFunctor, underlying, Category.assoc,
      MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
      Preadditive.comp_add, Preadditive.add_comp]

set_option backward.isDefEq.respectTransparency false in
instance underlyingFunctor_linear (C : BraidedFusionCategory.{v,u}) :
    (underlyingFunctor C).Linear ℂ where
  map_smul := by
    intro X Y f r
    apply CategoryTheory.Limits.biproduct.hom_ext'
    intro i
    apply CategoryTheory.Limits.biproduct.hom_ext
    intro j
    simp [underlyingFunctor, underlying, Category.assoc,
      MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
      Linear.comp_smul, Linear.smul_comp]

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- The underlying induction sum is faithful: any simple summand preserves
morphisms faithfully under both tensor factors. -/
instance underlyingFunctor_faithful (C : BraidedFusionCategory.{v,u}) :
    (underlyingFunctor C).Faithful where
  map_injective := by
    intro X Y f g h
    let i := unitIndex C
    let S := simples C i
    let : Simple S := simples_simple C i
    let : Simple (Sᘁ) := by
      let : Simple (ᘁS) := simple_leftDual C S
      exact Simple.of_iso (leftDualIso HasLeftDual.exact
        (BraidedCategory.exactPairing_swap S (Sᘁ))).symm
    obtain ⟨s, r, hsr⟩ := unit_retract_leftDual_tensor S
    let : (tensorLeft S).Faithful := PropertyF.tensorLeft_faithful_of_unit_retract s r hsr
    obtain ⟨s', r', hsr'⟩ := unit_retract_leftDual_tensor (Sᘁ)
    let : (tensorLeft (Sᘁ)).Faithful :=
      PropertyF.tensorLeft_faithful_of_unit_retract s' r' hsr'
    let : (tensorRight (Sᘁ)).Faithful :=
      Functor.Faithful.of_iso (BraidedCategory.tensorLeftIsoTensorRight (Sᘁ))
    apply (tensorLeft S).map_injective
    apply (tensorRight (Sᘁ)).map_injective
    have hc := congrArg (fun k =>
      biproduct.ι (fun j : Fin (rank C) => (simples C j ⊗ X) ⊗ (simples C j)ᘁ) i ≫
      k ≫ biproduct.π (fun j : Fin (rank C) => (simples C j ⊗ Y) ⊗ (simples C j)ᘁ) i) h
    simpa [underlyingFunctor, underlying, Category.assoc, S, i] using hc

end PropertyF.Ground.CentreInduction
