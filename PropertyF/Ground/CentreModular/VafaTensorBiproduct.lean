module
public import PropertyF.Ground.CentreModular.VafaBiproduct
public import Mathlib.CategoryTheory.Monoidal.Preadditive

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
local instance (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    PreservesBinaryBiproducts (tensorLeft X) := preservesBinaryBiproducts_of_preservesBiproducts _

/-- The tensor determinant identity is closed under binary direct sums. -/
theorem fpDeterminant_tensor_biprod (C : BraidedFusionCategory.{v,u})
    (X Y Z : C.Obj) (a : Y ≅ Y) (b : Z ≅ Z)
    (ha : fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ a) = fpDimension C X • fpDeterminant C Y a)
    (hb : fpDeterminant C (X ⊗ Z) (Iso.refl X ⊗ᵢ b) = fpDimension C X • fpDeterminant C Z b) :
    fpDeterminant C (X ⊗ (Y ⊞ Z)) (Iso.refl X ⊗ᵢ biprod.mapIso a b) =
      fpDimension C X • fpDeterminant C (Y ⊞ Z) (biprod.mapIso a b) := by
  let e := Functor.mapBiprod (tensorLeft X) Y Z
  let A := biprod.mapIso (Iso.refl X ⊗ᵢ a) (Iso.refl X ⊗ᵢ b)
  have hc : Iso.refl X ⊗ᵢ biprod.mapIso a b = e ≪≫ A ≪≫ e.symm := by
    apply Iso.ext
    apply (cancel_epi e.inv).1
    apply biprod.hom_ext'
    · have hι : biprod.inl ≫ e.inv = X ◁ biprod.inl := by
        rw [Functor.mapBiprod_inv, biprod.inl_desc]
        rfl
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
      simp only [← Category.assoc, hι, tensorIso_hom, Iso.refl_hom, id_tensorHom,
        ← whiskerLeft_comp]
      simp only [A, biprod.mapIso_hom, tensorIso_hom,
        Iso.refl_hom, id_tensorHom]
      simp only [biprod.inl_map, whiskerLeft_comp, Category.assoc]
      exact (congrArg (fun f => (X ◁ a.hom) ≫ f) hι).symm
    · have hι : biprod.inr ≫ e.inv = X ◁ biprod.inr := by
        rw [Functor.mapBiprod_inv, biprod.inr_desc]
        rfl
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
      simp only [← Category.assoc, hι, tensorIso_hom, Iso.refl_hom, id_tensorHom,
        ← whiskerLeft_comp]
      simp only [A, biprod.mapIso_hom, tensorIso_hom,
        Iso.refl_hom, id_tensorHom]
      simp only [biprod.inr_map, whiskerLeft_comp, Category.assoc]
      exact (congrArg (fun f => (X ◁ b.hom) ≫ f) hι).symm
  rw [hc]
  have hd := fpDeterminant_conjugate C e.symm A
  change fpDeterminant C (X ⊗ (Y ⊞ Z)) (e ≪≫ A ≪≫ e.symm) = fpDeterminant C _ A at hd
  rw [hd, fpDeterminant_biprod, fpDeterminant_biprod, ha, hb, smul_add]

end PropertyF.Ground.CentreModular
