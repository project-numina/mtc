module
public import PropertyF.Ground.CentreInduction.FirstTriangle

/-! The underlying Hom-space transpose and its retraction. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The candidate adjunction transpose, considered on underlying Hom spaces.
Centrality of its values is not asserted. -/
def transposeUnderlying (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj) (X : C.Obj) :
    (Z.1 ⟶ X) →ₗ[ℂ] (Z.1 ⟶ underlying C X) :=
  (Linear.leftComp ℂ (underlying C X) (unitCandidate C Z)).comp
    ((underlyingFunctor C).mapLinearMap ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- Projection through the unit summand is a left inverse of the candidate
transpose on underlying maps. -/
theorem transposeUnderlying_counit (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj) (X : C.Obj) (g : Z.1 ⟶ X) :
    transposeUnderlying C Z X g ≫ (underlyingCounit C).app X = g := by
  change (unitCandidate C Z ≫ (underlyingFunctor C).map g) ≫
    (underlyingCounit C).app X = g
  rw [Category.assoc, (underlyingCounit C).naturality g]
  simpa [Category.assoc] using congrArg (fun f => f ≫ g) (unitCandidate_counit C Z)

set_option backward.isDefEq.respectTransparency false in
/-- The candidate transpose is injective even before the induction
half-braiding and adjunction have been constructed. -/
theorem transposeUnderlying_injective (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj) (X : C.Obj) :
    Function.Injective (transposeUnderlying C Z X) := by
  intro f g h
  have hh := congrArg (fun k => k ≫ (underlyingCounit C).app X) h
  simpa only [transposeUnderlying_counit] using hh

end PropertyF.Ground.CentreInduction
