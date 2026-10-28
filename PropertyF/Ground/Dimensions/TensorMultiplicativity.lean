module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Calculus.PartialTrace

/-! # Tensor products of pivotal traces

Partial traces establish multiplicativity of the pivotal trace on tensor products.

## Main results

* `rightTraceWith_partialTraceWith`: computes the total trace using an arbitrary double-dual partial trace.
* `pivotalTrace_tensor`: proves multiplicativity of pivotal traces on tensor products.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor comparison of two arbitrary double-dual components. -/
theorem rightTraceWith_tensor_pairing {X Y : C} (j : X ≅ (Xᘁ)ᘁ) (k : Y ≅ (Yᘁ)ᘁ)
    (f : X ⊗ Y ⟶ X ⊗ Y) :
  (rightTraceWith ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) f).asHom =
    η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) ≫
      ((f ≫ (j.hom ⊗ₘ k.hom)) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
      ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := by
  let p1 : ExactPairing (X ⊗ Y) ((X ⊗ Y)ᘁ) := HasRightDual.exact
  let p2 : ExactPairing (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := ExactPairing.tensor
  let q1 : ExactPairing ((Yᘁ) ⊗ (Xᘁ)) (((Yᘁ) ⊗ (Xᘁ))ᘁ) := HasRightDual.exact
  let q2 : ExactPairing ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
  let r := rightDualIso p1 p2
  let s := rightDualIso q1 q2
  let u := f ≫ (j.hom ⊗ₘ k.hom)
  have ht := trace_change_rightDual p1 p2 (u ≫ s.inv)
  have hr : @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      ((u ≫ s.inv) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Yᘁ) ⊗ (Xᘁ))ᘁ) q1 =
      @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      (u ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) q2 := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight, Category.assoc]
    rw [(rightDualIso_inv_evaluation q1 q2)]
  have h := ht.trans hr
  simpa only [rightTraceWith, End.homEquiv_apply, doubleDualTensorIso, Iso.trans_hom,
    Iso.symm_hom, tensorIso_hom, rightDualIsoMap, Category.assoc, rightDualTensorIso,
    r, s, u, p1, p2, q1, q2] using h


/-- Close the right tensor factor using an arbitrary double-dual isomorphism. -/
def partialTraceWith {Y : C} (k : Y ≅ (Yᘁ)ᘁ) (X : C) (f : End (X ⊗ Y)) : End X :=
  End.of ((ρ_ X).inv ≫ (X ◁ η_ Y (Yᘁ)) ≫ (α_ X Y (Yᘁ)).inv ≫
    (f.asHom ▷ (Yᘁ)) ≫ (α_ X Y (Yᘁ)).hom ≫
    (X ◁ (k.hom ▷ (Yᘁ))) ≫ (X ◁ ε_ (Yᘁ) ((Yᘁ)ᘁ)) ≫ (ρ_ X).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Closing the right factor first works without a pivotal structure. -/
theorem rightTraceWith_partialTraceWith {X Y : C} (j : X ≅ (Xᘁ)ᘁ) (k : Y ≅ (Yᘁ)ᘁ)
    (f : End (X ⊗ Y)) :
    rightTraceWith j (partialTraceWith k X f).asHom =
      rightTraceWith ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) f.asHom := by
  apply End.homEquiv.injective
  change (rightTraceWith j (partialTraceWith k X f).asHom).asHom =
    (rightTraceWith ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) f.asHom).asHom
  rw [rightTraceWith_tensor_pairing]
  simp only [rightTraceWith, partialTraceWith]
  have hc : η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      η_ X (Xᘁ) ⊗≫ (X ◁ η_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫ 𝟙 _ := rfl
  have he : ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) =
      𝟙 (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ⊗ (Yᘁ ⊗ Xᘁ)) ⊗≫ ((Xᘁ)ᘁ : C) ◁ (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := rfl
  rw [hc, he]
  simp only [tensorHom_def, comp_whiskerRight]
  monoidal
  simp
  rw [whisker_exchange_assoc j.hom (λ_ (Xᘁ)).hom,
    whisker_exchange_assoc j.hom (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ)),
    whisker_exchange_assoc j.hom (k.hom ▷ (Yᘁ) ▷ (Xᘁ)),
    ← associator_naturality_left_assoc j.hom (Y ⊗ Yᘁ) (Xᘁ),
    ← comp_whiskerRight_assoc, ← associator_naturality_left, comp_whiskerRight, Category.assoc]


end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Closing the right tensor factor and then the left gives the total pivotal trace. -/
theorem rightTrace_partialTrace (p : PivotalStructure (C := C)) {X Y : C} (f : End (X ⊗ Y)) :
  p.rightTrace (rightPartialTrace p f).asHom = p.rightTrace f.asHom := by
  simpa only [rightTraceWith, PivotalStructure.rightTrace, partialTraceWith,
    rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk, Iso.trans_hom, tensorIso_hom,
    ← p.tensor X Y, Category.assoc] using rightTraceWith_partialTraceWith (p.iso X) (p.iso Y) f

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Calculus

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The partial trace on a simple object is its normalized total trace. -/
theorem rightPartialTrace_simple [CategoryTheory.Limits.HasKernels C] {X Y : C}
    [Simple X] [FiniteDimensional ℂ (X ⟶ X)] (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (f : End (X ⊗ Y))
    (hd : scalar (p.rightTrace (𝟙 X)) ≠ 0) :
    rightPartialTrace p f =
      (scalarTrace p scalar f / scalar (p.rightTrace (𝟙 X))) • (1 : End X) := by
  simpa only [scalarTrace, Dimensions.rightTrace_partialTrace p f] using
    simple_end_eq_trace_smul p scalar (rightPartialTrace p f) hd

end PropertyF.Ground.Calculus

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Closing the right tensor factor of an inserted endomorphism. -/
theorem rightPartialTrace_tensor_right (p : PivotalStructure (C := C)) (X : C) {Y : C} (b : Y ⟶ Y) :
    rightPartialTrace p (End.of (𝟙 X ⊗ₘ b)) =
      End.of ((ρ_ X).inv ≫ X ◁ (p.rightTrace b).asHom ≫ (ρ_ X).hom) := by
  apply End.ext
  simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    PivotalStructure.rightTrace, tensorHom_def, id_whiskerRight, Category.id_comp,
    whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  monoidal

/-- The right partial trace of an inserted right-factor endomorphism is scalar. -/
theorem rightPartialTrace_one_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X : C) {Y : C} (b : Y ⟶ Y) :
    rightPartialTrace p (End.of (𝟙 X ⊗ₘ b)) = scalar (p.rightTrace b) • 1 := by
  rw [rightPartialTrace_tensor_right p X b, eq_smul_one_of_algEquiv scalar (p.rightTrace b)]
  apply End.ext
  simp

/-- The partial trace of a tensor product is the left factor times the trace of the right. -/
theorem rightPartialTrace_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) {X Y : C} (a : X ⟶ X) (b : Y ⟶ Y) :
    rightPartialTrace p (End.of (a ⊗ₘ b)) = scalar (p.rightTrace b) • End.of a := by
  rw [show End.of (a ⊗ₘ b) = End.of (𝟙 X ⊗ₘ b) * insertRightIdentity Y (End.of a) from
      End.ext (by simp [insertRightIdentity, tensorHom_def]),
    rightPartialTrace_right, rightPartialTrace_one_tensor p scalar X b]
  simp

/-- Pivotal trace is multiplicative on tensor products of endomorphisms. -/
theorem pivotalTrace_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) {X Y : C} (a : X ⟶ X) (b : Y ⟶ Y) :
    scalar (p.rightTrace (a ⊗ₘ b)) = scalar (p.rightTrace a) * scalar (p.rightTrace b) := by
  have h := rightTrace_partialTrace p (End.of (a ⊗ₘ b))
  rw [rightPartialTrace_tensor p scalar a b] at h
  simpa [PivotalStructure.rightTrace_smul, smul_eq_mul, mul_comm] using congrArg scalar h.symm

end PropertyF.Ground.Dimensions

end
