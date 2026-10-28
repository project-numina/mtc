module
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Centre.Basic

/-! Detect centre morphisms on a finite set of simple objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- To check the centre-intertwining equation it suffices to test the simple
representatives of the underlying semisimple category. -/
theorem comm_of_simples (C : BraidedFusionCategory.{v,u})
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1)
    (h : ∀ i, (f ▷ simples C i) ≫ (Y.2.β (simples C i)).hom =
      (X.2.β (simples C i)).hom ≫ (simples C i ◁ f)) :
    ∀ U : C.Obj, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f) := by
  intro U
  let V := Dimensions.simplePiecesObject C U
  let e := Dimensions.simpleDecomposition C U
  apply (cancel_epi (X.1 ◁ e.inv)).1
  apply (cancel_epi (leftDistributor X.1 V).inv).1
  apply biproduct.hom_ext'
  intro p
  have hp := h p.1
  have hx := X.2.naturality (biproduct.ι V p ≫ e.inv)
  have hy := Y.2.naturality (biproduct.ι V p ≫ e.inv)
  let q : V p ⟶ U := biproduct.ι V p ≫ e.inv
  change (X.1 ◁ q) ≫ (X.2.β U).hom = (X.2.β (V p)).hom ≫ (q ▷ X.1) at hx
  have hp' : (f ▷ V p) ≫ (Y.2.β (V p)).hom =
      (X.2.β (V p)).hom ≫ (V p ◁ f) := hp
  have hs : (X.1 ◁ q) ≫ (f ▷ U) ≫ (Y.2.β U).hom =
      (X.1 ◁ q) ≫ (X.2.β U).hom ≫ (U ◁ f) := by
    calc
      _ = (f ▷ V p) ≫ ((Y.1 ◁ q) ≫ (Y.2.β U).hom) := by
        rw [whisker_exchange_assoc]
      _ = (f ▷ V p) ≫ ((Y.2.β (V p)).hom ≫ (q ▷ Y.1)) := by rw [hy]
      _ = (X.2.β (V p)).hom ≫ (V p ◁ f) ≫ (q ▷ Y.1) := by rw [← Category.assoc, hp']; simp [Category.assoc]
      _ = (X.2.β (V p)).hom ≫ ((q ▷ X.1) ≫ (U ◁ f)) := by rw [whisker_exchange]
      _ = _ := by simpa only [Category.assoc] using congrArg (fun k => k ≫ (U ◁ f)) hx.symm
  simpa only [biproduct_ι_comp_leftDistributor_inv_assoc, q,
    MonoidalCategory.whiskerLeft_comp, Category.assoc] using hs

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u v' u'
attribute [local instance] Abelian.hasFiniteBiproducts



end PropertyF.Ground.CentreInduction
