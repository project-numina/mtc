module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Calculus.PartialTrace

/-! # Tensor products of pivotal traces

Partial traces establish multiplicativity of the pivotal trace on tensor products.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The pivotal trace on a tensor product can be evaluated using the tensor
product exact pairings, independently of the chosen dual of the tensor product. -/
theorem rightTrace_tensor_pairing (p : PivotalStructure (C := C)) (X Y : C) (f : X ⊗ Y ⟶ X ⊗ Y) :
  (p.rightTrace f).asHom =
    η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) ≫
      ((f ≫ ((p.iso X).hom ⊗ₘ (p.iso Y).hom)) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
      ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := by
  let p1 : ExactPairing (X ⊗ Y) ((X ⊗ Y)ᘁ) := HasRightDual.exact
  let p2 : ExactPairing (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := ExactPairing.tensor
  let q1 : ExactPairing ((Yᘁ) ⊗ (Xᘁ)) (((Yᘁ) ⊗ (Xᘁ))ᘁ) := HasRightDual.exact
  let q2 : ExactPairing ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
  let r := rightDualIso p1 p2
  let s := rightDualIso q1 q2
  let u := f ≫ ((p.iso X).hom ⊗ₘ (p.iso Y).hom)
  have ht := trace_change_rightDual p1 p2 (u ≫ s.inv)
  dsimp only [PivotalStructure.rightTrace]
  rw [p.tensor X Y]
  have hr : @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      ((u ≫ s.inv) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Yᘁ) ⊗ (Xᘁ))ᘁ) q1 =
      @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      (u ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) q2 := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight, Category.assoc]
    rw [(rightDualIso_inv_evaluation q1 q2)]
  have h := ht.trans hr
  simpa only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap,
    Category.assoc, rightDualTensorIso, r, s, u, p1, p2, q1, q2] using h

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
theorem rightTrace_partialTrace (p : PivotalStructure (C := C)) (X Y : C) (f : End (X ⊗ Y)) :
  p.rightTrace (rightPartialTrace p X Y f).asHom = p.rightTrace f.asHom := by
  apply End.homEquiv.injective
  change (p.rightTrace (rightPartialTrace p X Y f).asHom).asHom = (p.rightTrace f.asHom).asHom
  rw [rightTrace_tensor_pairing]
  simp only [PivotalStructure.rightTrace, rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk]
  have hc : η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      η_ X (Xᘁ) ⊗≫ (X ◁ η_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫ 𝟙 _ := rfl
  have he : ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) =
      𝟙 (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ⊗ (Yᘁ ⊗ Xᘁ)) ⊗≫ ((Xᘁ)ᘁ : C) ◁ (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := rfl
  rw [hc, he]
  simp only [tensorHom_def, comp_whiskerRight]
  monoidal
  simp
  rw [whisker_exchange_assoc (p.iso X).hom (λ_ (Xᘁ)).hom]
  rw [whisker_exchange_assoc (p.iso X).hom (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ))]
  rw [whisker_exchange_assoc (p.iso X).hom ((p.iso Y).hom ▷ (Yᘁ) ▷ (Xᘁ))]
  rw [← associator_naturality_left_assoc (p.iso X).hom (Y ⊗ Yᘁ) (Xᘁ)]
  rw [← comp_whiskerRight_assoc, ← associator_naturality_left]

  rw [comp_whiskerRight, Category.assoc]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Closing the right tensor factor of an inserted endomorphism. -/
theorem rightPartialTrace_tensor_right (p : PivotalStructure (C := C)) (X Y : C) (b : Y ⟶ Y) :
    rightPartialTrace p X Y (End.of (𝟙 X ⊗ₘ b)) =
      End.of ((ρ_ X).inv ≫ X ◁ (p.rightTrace b).asHom ≫ (ρ_ X).hom) := by
  apply End.ext
  simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    PivotalStructure.rightTrace, tensorHom_def, id_whiskerRight, Category.id_comp,
    whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  monoidal

/-- The right partial trace of an inserted right-factor endomorphism is scalar. -/
theorem rightPartialTrace_one_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X Y : C) (b : Y ⟶ Y) :
    rightPartialTrace p X Y (End.of (𝟙 X ⊗ₘ b)) = scalar (p.rightTrace b) • 1 := by
  rw [rightPartialTrace_tensor_right p X Y b,
    show p.rightTrace b = scalar (p.rightTrace b) • (1 : End (𝟙_ C)) from
      scalar.injective (by simp)]
  apply End.ext
  simp

/-- The partial trace of a tensor product is the left factor times the trace of the right. -/
theorem rightPartialTrace_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X Y : C) (a : X ⟶ X) (b : Y ⟶ Y) :
    rightPartialTrace p X Y (End.of (a ⊗ₘ b)) = scalar (p.rightTrace b) • End.of a := by
  rw [show End.of (a ⊗ₘ b) = End.of (𝟙 X ⊗ₘ b) * insertRightIdentity X Y (End.of a) from
      End.ext (by simp [insertRightIdentity, tensorHom_def]),
    rightPartialTrace_right, rightPartialTrace_one_tensor p scalar X Y b]
  simp

/-- Pivotal trace is multiplicative on tensor products of endomorphisms. -/
theorem pivotalTrace_tensor (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X Y : C) (a : X ⟶ X) (b : Y ⟶ Y) :
    scalar (p.rightTrace (a ⊗ₘ b)) = scalar (p.rightTrace a) * scalar (p.rightTrace b) := by
  have h := rightTrace_partialTrace p X Y (End.of (a ⊗ₘ b))
  rw [rightPartialTrace_tensor p scalar X Y a b] at h
  have hs : p.rightTrace (a ⊗ₘ b) = scalar (p.rightTrace b) • p.rightTrace a := by
    simpa [PivotalStructure.rightTrace_smul] using h.symm
  rw [hs, map_smul]
  simp [mul_comm]

end PropertyF.Ground.Dimensions

end
