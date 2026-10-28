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

set_option backward.isDefEq.respectTransparency false in
/-- Natural transformations between additive functors out of a fusion
category are determined by their components on the simple representatives. -/
theorem natTrans_ext_on_simples (C : BraidedFusionCategory.{v,u})
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
    (F G : C.Obj ⥤ D) [F.Additive] [G.Additive] (a b : F ⟶ G)
    (h : ∀ i, a.app (simples C i) = b.app (simples C i)) : a = b := by
  ext U
  let V := Dimensions.simplePiecesObject C U
  let e := Dimensions.simpleDecomposition C U
  apply (cancel_epi (F.map e.inv)).1
  apply (cancel_epi (F.mapBiproduct V).inv).1
  apply biproduct.hom_ext'
  intro p
  simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc]
  rw [a.naturality, b.naturality, a.naturality_assoc, b.naturality_assoc]
  change a.app (simples C p.1) ≫ _ = b.app (simples C p.1) ≫ _
  rw [h p.1]

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation between additive functors is invertible at every
object if it is invertible on the simple representatives. -/
theorem natTrans_isIso_of_simples
    (C : BraidedFusionCategory.{v,u})
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
    (F G : C.Obj ⥤ D) [F.Additive] [G.Additive] (a : F ⟶ G)
    (h : ∀ i, IsIso (a.app (simples C i))) : ∀ T, IsIso (a.app T) := by
  classical
  intro T
  let V := Dimensions.simplePiecesObject C T
  let e := Dimensions.simpleDecomposition C T
  letI (p : Σ i : Fin (rank C), Fin (Module.finrank ℂ (simples C i ⟶ T))) : IsIso (a.app (V p)) := h p.1
  let k : F.obj (⨁ V) ≅ G.obj (⨁ V) := F.mapBiproduct V ≪≫
    biproduct.mapIso (fun p => asIso (a.app (V p))) ≪≫ (G.mapBiproduct V).symm
  have hk : a.app (⨁ V) = k.hom := by
    apply (cancel_mono (G.mapBiproduct V).hom).1
    apply (cancel_epi (F.mapBiproduct V).inv).1
    simp only [k, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, biproduct.mapIso_hom]
    apply biproduct.hom_ext'
    intro p
    simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
      a.naturality_assoc, biproduct.ι_map, asIso_hom, Category.assoc]
    have hp : G.map (biproduct.ι V p) ≫ (G.mapBiproduct V).hom =
        biproduct.ι (G.obj ∘ V) p := by
      rw [show G.map (biproduct.ι V p) =
        biproduct.ι (G.obj ∘ V) p ≫ (G.mapBiproduct V).inv by simp [Functor.mapBiproduct_inv]]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hp]
    rfl
  haveI : IsIso (a.app (⨁ V)) := by rw [hk]; infer_instance
  have hn := a.naturality e.inv
  have heq : a.app T = F.map e.hom ≫ a.app (⨁ V) ≫ G.map e.inv := by
    rw [← hn, ← Category.assoc, ← F.map_comp]
    simp
  rw [heq]
  infer_instance

end PropertyF.Ground.CentreInduction
