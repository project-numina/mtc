module
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.Dimensions.DualTensorNaturality

open PropertyF.Ground.Dimensions

/-! # Centre dual comparisons

The forgetful functor preserves right duals up to a natural isomorphism. Its double-dual
comparison satisfies the tensor and unit laws used to transport pivotal components.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RightRigidCategory (Center D)]
local notation "𝒵" => Center D
-- The dual and double-dual comparisons for the forgetful functor.
local notation "κ" => forgetDualIso
local notation "κ₂" => forgetDoubleDualIso
variable {X Y : Center D}

omit [RightRigidCategory D] in
/-- Forgetting a centre mate computes the mate for the forgotten dual pairings. -/
theorem forget_rightAdjointMate (f : X ⟶ Y) :
    (fᘁ).f = @rightAdjointMate D _ _ X.1 Y.1
      (show HasRightDual X.1 from { rightDual := (Xᘁ).1, exact := forgetPairing X })
      (show HasRightDual Y.1 from { rightDual := (Yᘁ).1, exact := forgetPairing Y }) f.f := by
  simp [rightAdjointMate]
  rfl

/-- The canonical comparison of centre and base duals is natural in centre morphisms. -/
theorem forgetDualIso_natural (f : X ⟶ Y) :
    (fᘁ).f ≫ (κ X).hom = (κ Y).hom ≫ (f.fᘁ) := by
  simp [forget_rightAdjointMate, forgetDualIso, rightDualIso, ← comp_rightAdjointMate]

/-- The double-dual comparison is natural in centre morphisms. -/
theorem forgetDoubleDualIso_natural (f : X ⟶ Y) :
    ((fᘁ)ᘁ).f ≫ (κ₂ Y).hom = (κ₂ X).hom ≫ ((f.fᘁ)ᘁ) := by
  simpa [forgetDoubleDualIso, rightDualIsoMap, Category.assoc] using (CommSq.vert_comp ⟨forgetDualIso_natural (fᘁ)⟩ ⟨by
      simpa only [comp_rightAdjointMate] using (congrArg (fun m => rightAdjointMate m)
        (CommSq.vert_inv (g := κ Y) (h := κ X) ⟨forgetDualIso_natural f⟩).w).symm⟩).w

variable (p : PivotalStructure (C := D))

/-- Transport a pivotal component along the forgotten double-dual comparison. -/
def transportedPivotalHom (Z : 𝒵) :
    Z.1 ⟶ ((Zᘁ)ᘁ).1 := (p.iso Z.1).hom ≫ (κ₂ Z).inv

/-- Transported pivotal components are isomorphisms in the base category. -/
instance transportedPivotalHom_isIso (Z : 𝒵) : IsIso (transportedPivotalHom p Z) :=
  inferInstanceAs (IsIso ((p.iso Z.1).hom ≫ (κ₂ Z).inv))

/-- The transported pivotal components are natural on centre morphisms. -/
theorem transported_pivotal_natural (f : X ⟶ Y) :
    f.f ≫ transportedPivotalHom p Y = transportedPivotalHom p X ≫ ((fᘁ)ᘁ).f :=
  (cancel_mono (κ₂ Y).hom).1 <| by
    simpa [transportedPivotalHom, Category.assoc, forgetDoubleDualIso_natural] using p.naturality f.f

end PropertyF.Ground.CentreInduction

end

/-! Tensor coherence of centre and base dual comparisons. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RightRigidCategory (Center D)]
local notation "𝒵" => Center D
-- The dual comparison for the forgetful functor.
local notation "κ" => forgetDualIso
variable (X Y : Center D)

omit [RightRigidCategory D] in
/-- Tensor the forgotten dual pairings of two centre objects. -/
abbrev tensorForgetPairing :
    ExactPairing (X.1 ⊗ Y.1) ((Yᘁ).1 ⊗ (Xᘁ).1) :=
  @ExactPairing.tensor D _ _ X.1 Y.1 (Xᘁ).1 (Yᘁ).1 (forgetPairing X) (forgetPairing Y)

omit [RightRigidCategory D] in
/-- The forgotten tensor dual agrees with the tensor pairing of forgotten duals. -/
theorem forget_rightDualTensorIso :
    (rightDualTensorIso X Y).hom.f =
      (rightDualIso (forgetPairing (X ⊗ Y)) (tensorForgetPairing X Y)).hom :=
  forget_rightDualIso HasRightDual.exact ExactPairing.tensor (tensorForgetPairing X Y) <| by
    simp [ExactPairing.tensor_coevaluation, monoidalComp]
    rfl

/-- Forgetting centre duals preserves their tensor comparison. -/
theorem forgetDualIso_tensor :
    (κ (X ⊗ Y)).hom ≫ (rightDualTensorIso X.1 Y.1).hom =
      (rightDualTensorIso X Y).hom.f ≫
        ((κ Y).hom ⊗ₘ (κ X).hom) := by
  rw [forget_rightDualTensorIso]
  simp only [forgetDualIso, rightDualTensorIso,
    ← rightDualIso_tensor (forgetPairing X) HasRightDual.exact
      (forgetPairing Y) HasRightDual.exact, rightDualIso_trans]

end PropertyF.Ground.CentreInduction
end

open PropertyF.Ground.Dimensions

/-! Tensor coherence for the forgotten double-dual and pivotal components. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RightRigidCategory (Center D)]
local notation "𝒵" => Center D
-- The dual and double-dual comparisons for the forgetful functor.
local notation "κ" => forgetDualIso
local notation "κ₂" => forgetDoubleDualIso
-- The tensor comparisons for right duals and double right duals.
local notation "τ" => rightDualTensorIso
local notation "μ₂" => doubleDualTensorIso
variable (p : PivotalStructure (C := D)) (X Y : Center D)

/-- The inverse tensor comparison commutes with the forgotten dual isomorphisms. -/
private theorem forgetDualIso_tensor_inv :
    (τ X Y).inv.f ≫ (κ (X ⊗ Y)).hom =
      ((κ Y).hom ⊗ₘ (κ X).hom) ≫
        (τ X.1 Y.1).inv :=
  (CommSq.vert_inv (g := (Center.forget D).mapIso (τ X Y))
    (h := rightDualTensorIso X.1 Y.1) ⟨forgetDualIso_tensor X Y⟩).w.symm

/-- Taking mates of the tensor comparison also preserves its inverse. -/
private theorem forgetDualIso_tensor_mate_inv :
    (τ X Y).hom.fᘁ ≫ (κ (X ⊗ Y)).invᘁ =
      (((κ Y).inv ⊗ₘ (κ X).inv)ᘁ) ≫
        (τ X.1 Y.1).homᘁ :=
  by simpa only [comp_rightAdjointMate, tensorIso_inv] using
    congrArg (fun m => rightAdjointMate m) (CommSq.horiz_inv
      (f := κ (X ⊗ Y)) (i := (κ Y) ⊗ᵢ (κ X)) ⟨forgetDualIso_tensor X Y⟩).w

/-- Forgetting the centre preserves the tensor comparison for double duals. -/
theorem forgetDoubleDualIso_tensor :
    (μ₂ X Y).hom.f ≫ (κ₂ (X ⊗ Y)).hom =
      ((κ₂ X).hom ⊗ₘ (κ₂ Y).hom) ≫
        (μ₂ X.1 Y.1).hom := by
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Center.comp_f, forgetDoubleDualIso, Category.assoc,
    reassoc_of% forgetDualIso_natural, reassoc_of% forgetDualIso_tensor_inv (Yᘁ) (Xᘁ),
    forgetDualIso_tensor_mate_inv X Y,
    ← reassoc_of% rightDualTensorIso_inv_natural (κ Y).inv (κ X).inv,
    tensorHom_comp_tensorHom_assoc]


/-- The transported pivotal components satisfy the tensor law after forgetting. -/
theorem transported_pivotal_tensor :
    (transportedPivotalHom p X ⊗ₘ transportedPivotalHom p Y) ≫
      (μ₂ X Y).hom.f = transportedPivotalHom p (X ⊗ Y) :=
  (Iso.eq_comp_inv (κ₂ (X ⊗ Y))).2 <| by
    simpa [transportedPivotalHom, Category.assoc, forgetDoubleDualIso_tensor] using
      (p.tensor X.1 Y.1).symm

/-! Unit coherence of centre dual and pivotal comparisons. -/

/-- Forgetting preserves the unit comparison for right duals. -/
theorem forgetDualIso_unit :
    (κ (𝟙_ (𝒵))).hom ≫ (rightDualUnitIso (C := D)).hom =
    (rightDualUnitIso (C := 𝒵)).hom.f :=
  letI : HasRightDual (𝟙_ (𝒵)) := RightRigidCategory.rightDual _
  (rightDualIso_trans (forgetPairing (𝟙_ (𝒵))) HasRightDual.exact
    (inferInstance : ExactPairing (𝟙_ D) (𝟙_ D))).trans
      (forget_rightDualIso HasRightDual.exact exactPairingUnit exactPairingUnit
        (Center.rightUnitor_inv_f _)).symm

/-- Forgetting preserves the unit comparison for double right duals. -/
theorem forgetDoubleDualIso_unit :
    (doubleDualUnitIso (C := 𝒵)).hom.f ≫ (κ₂ (𝟙_ (𝒵))).hom =
    (doubleDualUnitIso (C := D)).hom := by
  let U := 𝟙_ (𝒵)
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (𝟙_ D) := RightRigidCategory.rightDual _
  let e := rightDualUnitIso (C := 𝒵)
  let b := rightDualUnitIso (C := D)
  have hu : (κ U).hom ≫ b.hom = e.hom.f := forgetDualIso_unit (D := D)
  have hv : e.inv.f ≫ (κ U).hom = b.inv :=
    (Iso.inv_comp_eq ((Center.forget D).mapIso e)).2 ((Iso.eq_comp_inv b).2 hu)
  simp only [doubleDualUnitIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Center.comp_f, forgetDoubleDualIso, Category.assoc]
  change e.inv.f ≫ (e.homᘁ).f ≫ (κ (Uᘁ)).hom ≫
      (κ U).invᘁ = b.inv ≫ b.homᘁ
  erw [reassoc_of% forgetDualIso_natural e.hom]
  rw [← hu, comp_rightAdjointMate, Category.assoc,
    ← Category.assoc e.inv.f, hv, ← comp_rightAdjointMate, Iso.inv_hom_id,
    rightAdjointMate_id, Category.comp_id]

/-- Transported pivotal components preserve the tensor unit after forgetting. -/
theorem transported_pivotal_unit :
    transportedPivotalHom p (𝟙_ (𝒵)) = (doubleDualUnitIso (C := 𝒵)).hom.f :=
  (Iso.comp_inv_eq (κ₂ (𝟙_ (𝒵)))).2 <|
    p.unit.trans (forgetDoubleDualIso_unit (D := D)).symm

end PropertyF.Ground.CentreInduction
