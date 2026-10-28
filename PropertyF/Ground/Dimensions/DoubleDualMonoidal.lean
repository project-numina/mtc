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
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Canonical right-dual tensor comparisons respect associativity. -/
theorem rightDualTensorIso_associativity (X Y Z : C)
    [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
    [HasRightDual (X ⊗ Y)] [HasRightDual (Y ⊗ Z)]
    [HasRightDual ((X ⊗ Y) ⊗ Z)] [HasRightDual (X ⊗ (Y ⊗ Z))] :
    (rightDualTensorIso (X ⊗ Y) Z).hom ≫
      (Zᘁ) ◁ (rightDualTensorIso X Y).hom =
    ((α_ X Y Z).invᘁ) ≫ (rightDualTensorIso X (Y ⊗ Z)).hom ≫
      (rightDualTensorIso Y Z).hom ▷ (Xᘁ) ≫ (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom := by
  let A := (X ⊗ Y) ⊗ Z
  let B := (Zᘁ) ⊗ ((Yᘁ) ⊗ (Xᘁ))
  let D := X ⊗ (Y ⊗ Z)
  let E := ((Zᘁ) ⊗ (Yᘁ)) ⊗ (Xᘁ)
  have ha : (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom ▷ A ≫
      ε_ A B = E ◁ (α_ X Y Z).hom ≫ ε_ D E := by
    simp only [A, B, D, E, ExactPairing.tensor_evaluation]
    monoidal
  apply evaluation_ext (X := A)
  simp only [comp_whiskerRight_assoc]
  rw [tensorPairing_evaluation_whiskerLeft (p := HasRightDual.exact) (q := ExactPairing.tensor)
    (r := HasRightDual.exact) (rightDualTensorIso X Y).hom (rightDualTensorIso_evaluation X Y),
    rightDualTensorIso_evaluation (X ⊗ Y) Z]
  symm
  rw [ha, ← whisker_exchange_assoc,
    tensorPairing_evaluation_whiskerRight (p := HasRightDual.exact) (q := HasRightDual.exact)
      (r := ExactPairing.tensor) (rightDualTensorIso Y Z).hom (rightDualTensorIso_evaluation Y Z),
    ← whisker_exchange_assoc, rightDualTensorIso_evaluation X (Y ⊗ Z),
    ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation,
    ← Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]

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
    (α_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ((Zᘁ)ᘁ)).hom ≫ ((Xᘁ)ᘁ) ◁ (doubleDualTensorIso Y Z).hom ≫
      (doubleDualTensorIso X (Y ⊗ Z)).hom := by
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
    apply (Iso.inv_comp_eq F).1
    rw [← Category.assoc E.inv D.inv C₀.hom]
    apply (Iso.comp_inv_eq C₀).1
    simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc] using (congrArg Iso.inv heq).symm
  simp only [A, B, C₀, D, E, F, rightDualIsoMap, Iso.symm_hom,
    whiskerRightIso_hom, whiskerLeftIso_inv] at hrev
  rw [reassoc_of% hmove1, reassoc_of% hrev, reassoc_of% hdual,
    ← comp_rightAdjointMate_assoc, Iso.hom_inv_id, rightAdjointMate_id, Category.id_comp,
    ← (comp_rightAdjointMate (f := (α_ X Y Z).homᘁ) (g := (α_ X Y Z).invᘁ)),
    ← (comp_rightAdjointMate (f := (α_ X Y Z).inv) (g := (α_ X Y Z).hom)),
    Iso.inv_hom_id, rightAdjointMate_id, rightAdjointMate_id, Category.comp_id,
    reassoc_of% hmove2]

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
  associativity := fun X Y Z ↦ doubleDualTensorIso_associativity X Y Z
  left_unitality := fun X ↦ (doubleDualTensorIso_unit_left X).symm
  right_unitality := fun X ↦ (doubleDualTensorIso_unit_right X).symm

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
  rw [comp_rightAdjointMate, comp_rightAdjointMate] at hd
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc,
    hd, reassoc_of%
      ((CommSq.vert_inv (CommSq.mk (rightDualTensorIso_braiding (Xᘁ) (Yᘁ)))).w).symm]
end PropertyF.Ground.Dimensions
