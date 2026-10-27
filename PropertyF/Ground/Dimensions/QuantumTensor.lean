module
public import PropertyF.Ground.Dimensions.TensorTrace
public import PropertyF.Ground.Dimensions.GroundNorm

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
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
  have he := rightDualIso_inv_evaluation q1 q2
  have hr : @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      ((u ≫ s.inv) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Yᘁ) ⊗ (Xᘁ))ᘁ) q1 =
      @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      (u ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) q2 := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight, Category.assoc]
    rw [he]
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
  have h : (rightTraceWith ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) f.asHom).asHom =
    η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) ≫
      ((f.asHom ≫ (j.hom ⊗ₘ k.hom)) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
      ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := by
    exact rightTraceWith_tensor_pairing j k f.asHom
  rw [h]
  simp only [rightTraceWith, partialTraceWith]
  have hc : η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      η_ X (Xᘁ) ⊗≫ (X ◁ η_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫ 𝟙 _ := rfl
  have he : ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) =
      𝟙 (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ⊗ (Yᘁ ⊗ Xᘁ)) ⊗≫ ((Xᘁ)ᘁ : C) ◁ (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := rfl
  rw [hc, he]
  simp only [tensorHom_def, comp_whiskerRight]
  monoidal
  simp
  rw [whisker_exchange_assoc j.hom (λ_ (Xᘁ)).hom]
  rw [whisker_exchange_assoc j.hom (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ))]
  rw [whisker_exchange_assoc j.hom (k.hom ▷ (Yᘁ) ▷ (Xᘁ))]
  rw [← associator_naturality_left_assoc j.hom (Y ⊗ Yᘁ) (Xᘁ)]
  rw [← comp_whiskerRight_assoc, ← associator_naturality_left]
  rw [comp_whiskerRight, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Closing an identity strand gives the right quantum trace as a scalar. -/
theorem partialTraceWith_one {Y : C} (k : Y ≅ (Yᘁ)ᘁ) (X : C) :
    partialTraceWith k X 1 =
      End.of ((ρ_ X).inv ≫ X ◁ (rightQuantumTrace k).asHom ≫ (ρ_ X).hom) := by
  apply End.ext
  simp only [partialTraceWith, rightQuantumTrace, End.one_asHom,
    id_whiskerRight, Category.id_comp, whiskerLeft_comp, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Quantum dimensions multiply for any two double-dual isomorphisms, without
a naturality or pivotal assumption. -/
theorem rightQuantumTrace_tensor_scalar
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) {X Y : C}
    (j : X ≅ (Xᘁ)ᘁ) (k : Y ≅ (Yᘁ)ᘁ) :
    scalar (rightQuantumTrace ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y)) =
      scalar (rightQuantumTrace j) * scalar (rightQuantumTrace k) := by
  have hscalar : rightQuantumTrace k = scalar (rightQuantumTrace k) • (1 : End (𝟙_ C)) := by
    apply scalar.injective
    simp
  have hpt : partialTraceWith k X 1 = scalar (rightQuantumTrace k) • 1 := by
    rw [partialTraceWith_one, hscalar]
    apply End.ext
    simp
  have h := rightTraceWith_partialTraceWith j k (1 : End (X ⊗ Y))
  rw [hpt] at h
  have ht : rightQuantumTrace ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) =
      scalar (rightQuantumTrace k) • rightQuantumTrace j := by
    apply End.homEquiv.injective
    have hh := congrArg End.asHom h.symm
    simpa [rightTraceWith, rightQuantumTrace, tensorHom_def] using hh
  rw [ht, map_smul]
  simp [mul_comm]

end PropertyF.Ground.Dimensions
