module
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualUnitTensor

/-! # Monoidality of the double dual

Dual tensor comparisons make the double-dual functor monoidal and preserve the braiding.

## Main results

* `rightDualTensorIso_associativity`: proves associativity for the right-dual tensor comparison.
* `doubleDualCoreMonoidal`: packages the double-dual comparison as monoidal data.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- Canonical right-dual tensor comparisons respect associativity. -/
theorem rightDualTensorIso_associativity (X Y Z : C) :
    (rightDualTensorIso (X ⊗ Y) Z).hom ≫
      (Zᘁ) ◁ (rightDualTensorIso X Y).hom =
    ((α_ X Y Z).invᘁ) ≫ (rightDualTensorIso X (Y ⊗ Z)).hom ≫
      (rightDualTensorIso Y Z).hom ▷ (Xᘁ) ≫ (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom := by
  let A := (X ⊗ Y) ⊗ Z
  let B := (Zᘁ) ⊗ ((Yᘁ) ⊗ (Xᘁ))
  let qXY : ExactPairing (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := ExactPairing.tensor
  let : ExactPairing (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := qXY
  let qA : ExactPairing A B := @ExactPairing.tensor C _ _ (X ⊗ Y) Z ((Yᘁ) ⊗ (Xᘁ)) (Zᘁ)
    qXY HasRightDual.exact
  let : ExactPairing A B := qA
  let D := X ⊗ (Y ⊗ Z)
  let E := ((Zᘁ) ⊗ (Yᘁ)) ⊗ (Xᘁ)
  let qYZ : ExactPairing (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) := ExactPairing.tensor
  let qD : ExactPairing D E := @ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) ((Zᘁ) ⊗ (Yᘁ))
    HasRightDual.exact qYZ
  have ha : (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom ▷ A ≫
      @ExactPairing.evaluation C _ _ A B qA =
    E ◁ (α_ X Y Z).hom ≫ @ExactPairing.evaluation C _ _ D E qD := by
    rw [@ExactPairing.tensor_evaluation C _ _ (X ⊗ Y) Z _ _ qXY HasRightDual.exact,
      @ExactPairing.tensor_evaluation C _ _ X (Y ⊗ Z) _ _ HasRightDual.exact qYZ,
      @ExactPairing.tensor_evaluation C _ _ X Y _ _ HasRightDual.exact HasRightDual.exact,
      @ExactPairing.tensor_evaluation C _ _ Y Z _ _ HasRightDual.exact HasRightDual.exact]
    monoidal
  apply evaluation_ext (X := A)
  simp only [comp_whiskerRight_assoc]
  rw [tensorPairing_evaluation_whiskerLeft (p := HasRightDual.exact) (q := qXY)
    (r := HasRightDual.exact) (rightDualTensorIso X Y).hom (rightDualTensorIso_evaluation X Y),
    rightDualTensorIso_evaluation (X ⊗ Y) Z]
  symm
  rw [ha, ← whisker_exchange_assoc,
    tensorPairing_evaluation_whiskerRight (p := HasRightDual.exact) (q := HasRightDual.exact)
      (r := qYZ) (rightDualTensorIso Y Z).hom (rightDualTensorIso_evaluation Y Z),
    ← whisker_exchange_assoc, rightDualTensorIso_evaluation X (Y ⊗ Z),
    ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation]
  rw [← Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison respects associativity. -/
theorem doubleDualTensorIso_associativity (X Y Z : C) :
    (doubleDualTensorIso X Y).hom ▷ ((Zᘁ)ᘁ) ≫ (doubleDualTensorIso (X ⊗ Y) Z).hom ≫
      (((α_ X Y Z).homᘁ)ᘁ) =
    (α_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ((Zᘁ)ᘁ)).hom ≫
      ((Xᘁ)ᘁ) ◁ (doubleDualTensorIso Y Z).hom ≫ (doubleDualTensorIso X (Y ⊗ Z)).hom := by
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  have hmove1 : (rightDualTensorIso X Y).homᘁ ▷ ((Zᘁ)ᘁ) ≫
      (rightDualTensorIso (Zᘁ) ((X ⊗ Y)ᘁ)).inv =
    (rightDualTensorIso (Zᘁ) ((Yᘁ) ⊗ (Xᘁ))).inv ≫
      (((Zᘁ) ◁ (rightDualTensorIso X Y).hom)ᘁ) := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      rightDualTensorIso_inv_natural (𝟙 (Zᘁ)) (rightDualTensorIso X Y).hom
  have hmove2 : (rightDualTensorIso ((Zᘁ) ⊗ (Yᘁ)) (Xᘁ)).inv ≫
      (((rightDualTensorIso Y Z).hom ▷ (Xᘁ))ᘁ) =
    ((Xᘁ)ᘁ) ◁ ((rightDualTensorIso Y Z).homᘁ) ≫
      (rightDualTensorIso ((Y ⊗ Z)ᘁ) (Xᘁ)).inv := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      (rightDualTensorIso_inv_natural (rightDualTensorIso Y Z).hom (𝟙 (Xᘁ))).symm
  have hdual := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_associativity X Y Z)
  simp only [comp_rightAdjointMate] at hdual
  let A := (rightDualTensorIso (Yᘁ) (Xᘁ)).symm ▷ᵢ ((Zᘁ)ᘁ)
  let B := (rightDualTensorIso (Zᘁ) ((Yᘁ) ⊗ (Xᘁ))).symm
  let C₀ := rightDualIsoMap (α_ (Zᘁ) (Yᘁ) (Xᘁ)).symm
  let D := rightDualTensorIso ((Zᘁ) ⊗ (Yᘁ)) (Xᘁ)
  let E := ((Xᘁ)ᘁ) ◁ᵢ rightDualTensorIso (Zᘁ) (Yᘁ)
  let F := α_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ((Zᘁ)ᘁ)
  have heq : D ≪≫ E = C₀ ≪≫ B.symm ≪≫ A.symm ≪≫ F := by
    apply Iso.ext
    simpa only [A, B, C₀, D, E, F, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, rightDualIsoMap,
      whiskerRightIso_inv, whiskerLeftIso_hom] using
      rightDualTensorIso_associativity (Zᘁ) (Yᘁ) (Xᘁ)
  have hrev : A.hom ≫ B.hom = F.hom ≫ E.inv ≫ D.inv ≫ C₀.hom := by
    apply (cancel_epi F.inv).1
    apply (cancel_mono C₀.inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc] using (congrArg Iso.inv heq).symm
  simp only [A, B, C₀, D, E, F, rightDualIsoMap, Iso.symm_hom,
    whiskerRightIso_hom, whiskerLeftIso_inv] at hrev
  slice_lhs 2 3 => rw [hmove1]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hrev]
  simp only [Category.assoc]
  slice_lhs 5 6 => rw [hdual]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id]
  simp only [Category.id_comp, Category.assoc]
  slice_lhs 6 7 => rw [← comp_rightAdjointMate, ← comp_rightAdjointMate,
    Iso.inv_hom_id, rightAdjointMate_id, rightAdjointMate_id]
  simp only [Category.comp_id]
  slice_lhs 3 4 => rw [hmove2]
  simp only [Category.assoc]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual assignment is strongly monoidal. -/
def doubleDualCoreMonoidal (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] :
    (doubleDualFunctor C).CoreMonoidal where
  εIso := doubleDualUnitIso
  μIso := doubleDualTensorIso
  μIso_hom_natural_left := by
    intro X Y f X'
    simpa only [doubleDualFunctor, rightAdjointMate_id, tensorHom_id] using
      (doubleDualTensorIso_natural f (𝟙 X'))
  μIso_hom_natural_right := by
    intro X Y X' f
    simpa only [doubleDualFunctor, rightAdjointMate_id, id_tensorHom] using
      (doubleDualTensorIso_natural (𝟙 X') f)
  associativity := by
    intro X Y Z
    exact doubleDualTensorIso_associativity X Y Z
  left_unitality := by
    intro X
    exact (doubleDualTensorIso_unit_left X).symm
  right_unitality := by
    intro X
    exact (doubleDualTensorIso_unit_right X).symm

/-- The canonical monoidal structure on the double-dual functor. -/
@[instance_reducible] def doubleDualMonoidal (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] :
    (doubleDualFunctor C).Monoidal := (doubleDualCoreMonoidal C).toMonoidal
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison preserves the braiding. -/
theorem doubleDualTensorIso_braiding {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    (doubleDualTensorIso X Y).hom ≫ (((β_ X Y).homᘁ)ᘁ) =
      (β_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (doubleDualTensorIso Y X).hom := by
  have hd := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_braiding X Y)
  simp only [comp_rightAdjointMate] at hd
  have hm := ((CommSq.vert_inv (CommSq.mk (rightDualTensorIso_braiding (Xᘁ) (Yᘁ)))).w).symm
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc]
  rw [hd, ← Category.assoc, hm, Category.assoc]
end PropertyF.Ground.Dimensions
