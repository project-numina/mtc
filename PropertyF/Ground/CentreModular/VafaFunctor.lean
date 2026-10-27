module
public import PropertyF.Ground.CentreModular.AdditiveDecomposition
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Components of a natural automorphism of a functor are conjugate along
isomorphisms in the source. -/
theorem functor_natural_app_conjugate (C : BraidedFusionCategory.{v,u})
    (F : C.Obj ⥤ C.Obj) (η : F ≅ F) {X Y : C.Obj} (e : X ≅ Y) :
    η.app X = F.mapIso e ≪≫ η.app Y ≪≫ (F.mapIso e).symm := by
  apply Iso.ext
  have h := η.hom.naturality e.hom
  change F.map e.hom ≫ (η.app Y).hom = (η.app X).hom ≫ F.map e.hom at h
  change (η.app X).hom = F.map e.hom ≫ (η.app Y).hom ≫ F.map e.inv
  rw [← Category.assoc, h]
  simp [Category.assoc, ← F.map_comp]

/-- An additive functor's natural automorphism is block diagonal on a binary
biproduct under its canonical comparison isomorphism. -/
theorem functor_natural_app_biprod (C : BraidedFusionCategory.{v,u})
    (F : C.Obj ⥤ C.Obj) [F.Additive] [PreservesBinaryBiproducts F] (η : F ≅ F) (X Y : C.Obj) :
    η.app (X ⊞ Y) = F.mapBiprod X Y ≪≫
      biprod.mapIso (η.app X) (η.app Y) ≪≫ (F.mapBiprod X Y).symm := by
  let e := F.mapBiprod X Y
  apply Iso.ext
  change (η.app (X ⊞ Y)).hom = e.hom ≫ (biprod.mapIso (η.app X) (η.app Y)).hom ≫ e.inv
  apply (cancel_epi e.inv).1
  apply biprod.hom_ext'
  · have hι : biprod.inl ≫ e.inv = F.map biprod.inl := by
      rw [Functor.mapBiprod_inv, biprod.inl_desc]
    have hn := η.hom.naturality (biprod.inl : X ⟶ X ⊞ Y)
    change F.map biprod.inl ≫ (η.app (X ⊞ Y)).hom = (η.app X).hom ≫ F.map biprod.inl at hn
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hι, hn]
    simp only [biprod.mapIso_hom, biprod.inl_map_assoc, hι]
  · have hι : biprod.inr ≫ e.inv = F.map biprod.inr := by
      rw [Functor.mapBiprod_inv, biprod.inr_desc]
    have hn := η.hom.naturality (biprod.inr : Y ⟶ X ⊞ Y)
    change F.map biprod.inr ≫ (η.app (X ⊞ Y)).hom = (η.app Y).hom ≫ F.map biprod.inr at hn
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hι, hn]
    simp only [biprod.mapIso_hom, biprod.inr_map_assoc, hι]

/-- The FP determinant of a natural automorphism of an additive functor
expands over the simple summands of the source object. -/
theorem fpDeterminant_functor_natural_decomposition (C : BraidedFusionCategory.{v,u})
    (F : C.Obj ⥤ C.Obj) [F.Additive] (η : F ≅ F) (X : C.Obj) :
    fpDeterminant C (F.obj X) (η.app X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) •
        fpDeterminant C (F.obj (simples C i)) (η.app (simples C i)) := by
  apply additive_object_function_decomposition C vafaUnitSpace
    (fun X => fpDeterminant C (F.obj X) (η.app X))
  · intro X Y e
    rw [functor_natural_app_conjugate C F η e]
    exact fpDeterminant_conjugate C (F.mapIso e).symm (η.app Y)
  · intro X hX
    have hFX : IsZero (F.obj X) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      rw [← F.map_id, (IsZero.iff_id_eq_zero X).mp hX, F.map_zero]
    have hη : η.app X = Iso.refl (F.obj X) := by
      apply Iso.ext
      exact hFX.eq_of_src _ _
    rw [hη, fpDeterminant_refl]
  · intro X Y
    let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    rw [functor_natural_app_biprod C F η X Y]
    have h := fpDeterminant_conjugate C (F.mapBiprod X Y).symm
      (biprod.mapIso (η.app X) (η.app Y))
    change fpDeterminant C (F.obj (X ⊞ Y))
      (F.mapBiprod X Y ≪≫ biprod.mapIso (η.app X) (η.app Y) ≪≫ (F.mapBiprod X Y).symm) = _ at h
    rw [h, fpDeterminant_biprod]

end PropertyF.Ground.CentreModular
