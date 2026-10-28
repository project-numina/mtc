module
public import PropertyF.Ground.CentreInduction.ForgetDualTensor

open PropertyF.Ground.Dimensions

/-! Tensor coherence for the forgotten double-dual and pivotal components. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (Center D)]
local notation "𝒵" => Center D
variable (p : PivotalStructure (C := D)) (X Y : Center D)

/-- The inverse tensor comparison commutes with the forgotten dual isomorphisms. -/
private theorem forgetDualIso_tensor_inv :
    (rightDualTensorIso X Y).inv.f ≫ (forgetDualIso (X ⊗ Y)).hom =
      ((forgetDualIso Y).hom ⊗ₘ (forgetDualIso X).hom) ≫
        (rightDualTensorIso X.1 Y.1).inv :=
  (Iso.eq_comp_inv (rightDualTensorIso X.1 Y.1)).2 <|
    (Category.assoc _ _ _).trans <|
      (congrArg ((rightDualTensorIso X Y).inv.f ≫ ·) (forgetDualIso_tensor X Y)).trans <|
        ((Center.forget D).mapIso (rightDualTensorIso X Y)).inv_hom_id_assoc _

/-- Taking mates of the tensor comparison also preserves its inverse. -/
private theorem forgetDualIso_tensor_mate_inv :
    (rightDualTensorIso X Y).hom.fᘁ ≫ (forgetDualIso (X ⊗ Y)).invᘁ =
      (((forgetDualIso Y).inv ⊗ₘ (forgetDualIso X).inv)ᘁ) ≫
        (rightDualTensorIso X.1 Y.1).homᘁ := by
  let e := (forgetDualIso Y) ⊗ᵢ (forgetDualIso X)
  change (rightDualTensorIso X Y).hom.fᘁ ≫
      (rightDualIsoMap (forgetDualIso (X ⊗ Y))).inv =
    (rightDualIsoMap e).inv ≫ (rightDualTensorIso X.1 Y.1).homᘁ
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  simpa only [e, comp_rightAdjointMate, rightDualIsoMap, tensorIso_hom] using
    (congrArg (fun m => rightAdjointMate m) (forgetDualIso_tensor X Y)).symm

/-- Forgetting the centre preserves the tensor comparison for double duals. -/
theorem forgetDoubleDualIso_tensor :
    (doubleDualTensorIso X Y).hom.f ≫ (forgetDoubleDualIso (X ⊗ Y)).hom =
      ((forgetDoubleDualIso X).hom ⊗ₘ (forgetDoubleDualIso Y).hom) ≫
        (doubleDualTensorIso X.1 Y.1).hom := by
  dsimp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Center.comp_f, forgetDoubleDualIso]
  rw [Category.assoc, ← Category.assoc ((rightDualTensorIso X Y).homᘁ).f,
    forgetDualIso_natural]
  rw [← Category.assoc, ← Category.assoc, forgetDualIso_tensor_inv (Yᘁ) (Xᘁ)]
  rw [Category.assoc, forgetDualIso_tensor_mate_inv X Y, Category.assoc,
    ← Category.assoc ((rightDualTensorIso (Yᘁ).1 (Xᘁ).1).inv),
    ← rightDualTensorIso_inv_natural (forgetDualIso Y).inv (forgetDualIso X).inv]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]


/-- The transported pivotal components satisfy the tensor law after forgetting. -/
theorem transported_pivotal_tensor :
    (transportedPivotalHom p X ⊗ₘ transportedPivotalHom p Y) ≫
      (doubleDualTensorIso X Y).hom.f = transportedPivotalHom p (X ⊗ Y) := by
  dsimp only [transportedPivotalHom]
  rw [Iso.eq_comp_inv, Category.assoc, forgetDoubleDualIso_tensor]
  simpa [Category.assoc] using (p.tensor X.1 Y.1).symm

/-! Unit coherence of centre dual and pivotal comparisons. -/

omit [RightRigidCategory D] in
/-- The right-dual unit comparison is preserved by centre forget. -/
theorem forget_rightDualUnitIso :
    (rightDualUnitIso (C := 𝒵)).hom.f =
      (rightDualIso (forgetPairing (𝟙_ (𝒵)))
        (inferInstance : ExactPairing (𝟙_ D) (𝟙_ D))).hom :=
  forget_rightDualIso
    (@HasRightDual.exact (Center D) _ _ (𝟙_ (𝒵)) (RightRigidCategory.rightDual _))
    exactPairingUnit exactPairingUnit (Center.rightUnitor_inv_f _)

/-- Forgetting preserves the unit comparison for right duals. -/
theorem forgetDualIso_unit :
    (forgetDualIso (𝟙_ (𝒵))).hom ≫ (rightDualUnitIso (C := D)).hom =
    (rightDualUnitIso (C := 𝒵)).hom.f :=
  (rightDualIso_trans (forgetPairing (𝟙_ (𝒵))) HasRightDual.exact
    (inferInstance : ExactPairing (𝟙_ D) (𝟙_ D))).trans (forget_rightDualUnitIso (D := D)).symm

/-- Forgetting preserves the unit comparison for double right duals. -/
theorem forgetDoubleDualIso_unit :
    (doubleDualUnitIso (C := 𝒵)).hom.f ≫ (forgetDoubleDualIso (𝟙_ (𝒵))).hom =
    (doubleDualUnitIso (C := D)).hom := by
  let U := 𝟙_ (𝒵)
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (𝟙_ D) := RightRigidCategory.rightDual _
  let e := rightDualUnitIso (C := 𝒵)
  let b := rightDualUnitIso (C := D)
  have hu : (forgetDualIso U).hom ≫ b.hom = e.hom.f := forgetDualIso_unit (D := D)
  have hv : e.inv.f ≫ (forgetDualIso U).hom = b.inv :=
    (Iso.comp_hom_eq_id b).1 <| (Category.assoc _ _ _).trans <|
      (congrArg (e.inv.f ≫ ·) hu).trans (congrArg Center.Hom.f e.inv_hom_id)
  have hn := forgetDualIso_natural e.hom
  change (e.homᘁ).f ≫ (forgetDualIso (Uᘁ)).hom =
    (forgetDualIso U).hom ≫ (e.hom.fᘁ) at hn
  dsimp only [doubleDualUnitIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Center.comp_f, forgetDoubleDualIso]
  rw [Category.assoc]
  change e.inv.f ≫ (e.homᘁ).f ≫ (forgetDualIso (Uᘁ)).hom ≫
      (forgetDualIso U).invᘁ = b.inv ≫ b.homᘁ
  rw [← Category.assoc (e.homᘁ).f, hn, ← hu, comp_rightAdjointMate]
  rw [Category.assoc, ← Category.assoc e.inv.f, hv]
  simp only [← comp_rightAdjointMate, Iso.inv_hom_id_assoc]

/-- Transported pivotal components preserve the tensor unit after forgetting. -/
theorem transported_pivotal_unit :
    transportedPivotalHom p (𝟙_ (𝒵)) = (doubleDualUnitIso (C := 𝒵)).hom.f :=
  (Iso.comp_inv_eq (forgetDoubleDualIso (𝟙_ (𝒵)))).2 <|
    p.unit.trans (forgetDoubleDualIso_unit (D := D)).symm

end PropertyF.Ground.CentreInduction
