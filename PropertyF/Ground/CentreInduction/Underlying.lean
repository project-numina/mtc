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

/-- The induction sum is functorial in its middle factor. This is a functor
in the base category; its lift to the centre is still to be constructed. -/
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
