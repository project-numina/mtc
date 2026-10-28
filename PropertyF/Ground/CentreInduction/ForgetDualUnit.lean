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
  (CommSq.vert_inv (g := (Center.forget D).mapIso (rightDualTensorIso X Y))
    (h := rightDualTensorIso X.1 Y.1) ⟨forgetDualIso_tensor X Y⟩).w.symm

/-- Taking mates of the tensor comparison also preserves its inverse. -/
private theorem forgetDualIso_tensor_mate_inv :
    (rightDualTensorIso X Y).hom.fᘁ ≫ (forgetDualIso (X ⊗ Y)).invᘁ =
      (((forgetDualIso Y).inv ⊗ₘ (forgetDualIso X).inv)ᘁ) ≫
        (rightDualTensorIso X.1 Y.1).homᘁ :=
  (CommSq.vert_inv (g := rightDualIsoMap ((forgetDualIso Y) ⊗ᵢ (forgetDualIso X)))
    (h := rightDualIsoMap (forgetDualIso (X ⊗ Y))) ⟨by
      simpa only [comp_rightAdjointMate, rightDualIsoMap, tensorIso_hom] using
        congrArg (fun m => rightAdjointMate m) (forgetDualIso_tensor X Y)⟩).w

/-- Forgetting the centre preserves the tensor comparison for double duals. -/
theorem forgetDoubleDualIso_tensor :
    (doubleDualTensorIso X Y).hom.f ≫ (forgetDoubleDualIso (X ⊗ Y)).hom =
      ((forgetDoubleDualIso X).hom ⊗ₘ (forgetDoubleDualIso Y).hom) ≫
        (doubleDualTensorIso X.1 Y.1).hom := by
  dsimp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Center.comp_f, forgetDoubleDualIso]
  rw [Category.assoc, reassoc_of% forgetDualIso_natural,
    reassoc_of% forgetDualIso_tensor_inv (Yᘁ) (Xᘁ), forgetDualIso_tensor_mate_inv X Y,
    ← reassoc_of% rightDualTensorIso_inv_natural (forgetDualIso Y).inv (forgetDualIso X).inv,
    tensorHom_comp_tensorHom_assoc]


/-- The transported pivotal components satisfy the tensor law after forgetting. -/
theorem transported_pivotal_tensor :
    (transportedPivotalHom p X ⊗ₘ transportedPivotalHom p Y) ≫
      (doubleDualTensorIso X Y).hom.f = transportedPivotalHom p (X ⊗ Y) :=
  (Iso.eq_comp_inv (forgetDoubleDualIso (X ⊗ Y))).2 <| by
    simpa [transportedPivotalHom, Category.assoc, forgetDoubleDualIso_tensor] using
      (p.tensor X.1 Y.1).symm

/-! Unit coherence of centre dual and pivotal comparisons. -/

omit [RightRigidCategory D] in
/-- The right-dual unit comparison is preserved by centre forget. -/
theorem forget_rightDualUnitIso :
    (rightDualUnitIso (C := 𝒵)).hom.f =
      (rightDualIso (forgetPairing (𝟙_ (𝒵)))
        (inferInstance : ExactPairing (𝟙_ D) (𝟙_ D))).hom :=
  letI : HasRightDual (𝟙_ (𝒵)) := RightRigidCategory.rightDual _
  forget_rightDualIso HasRightDual.exact exactPairingUnit exactPairingUnit
    (Center.rightUnitor_inv_f _)

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
    (Iso.inv_comp_eq ((Center.forget D).mapIso e)).2 ((Iso.eq_comp_inv b).2 hu)
  have hn := forgetDualIso_natural e.hom
  change (e.homᘁ).f ≫ (forgetDualIso (Uᘁ)).hom =
    (forgetDualIso U).hom ≫ (e.hom.fᘁ) at hn
  dsimp only [doubleDualUnitIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Center.comp_f, forgetDoubleDualIso]
  rw [Category.assoc]
  change e.inv.f ≫ (e.homᘁ).f ≫ (forgetDualIso (Uᘁ)).hom ≫
      (forgetDualIso U).invᘁ = b.inv ≫ b.homᘁ
  rw [reassoc_of% hn, ← hu, comp_rightAdjointMate, Category.assoc,
    ← Category.assoc e.inv.f, hv, ← comp_rightAdjointMate, Iso.inv_hom_id,
    rightAdjointMate_id, Category.comp_id]

/-- Transported pivotal components preserve the tensor unit after forgetting. -/
theorem transported_pivotal_unit :
    transportedPivotalHom p (𝟙_ (𝒵)) = (doubleDualUnitIso (C := 𝒵)).hom.f :=
  (Iso.comp_inv_eq (forgetDoubleDualIso (𝟙_ (𝒵)))).2 <|
    p.unit.trans (forgetDoubleDualIso_unit (D := D)).symm

end PropertyF.Ground.CentreInduction
