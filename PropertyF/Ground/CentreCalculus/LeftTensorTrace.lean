module
public import PropertyF.Ground.CentreCalculus.LeftCrossing

/-! Tensor pairing identities for the left pivotal trace. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Coevaluation of the chosen dual of a tensor product, expressed in the
canonical tensor-dual pairing. -/
theorem tensorDual_coevaluation (X Y : C) :
    η_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ) =
      η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) ≫
        ((rightDualTensorIso X Y).inv ⊗ₘ (Dimensions.doubleDualTensorIso X Y).hom) := by
  let A := (X ⊗ Y)ᘁ
  let B := (Yᘁ) ⊗ (Xᘁ)
  let E := ((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)
  let r : A ≅ B := rightDualTensorIso X Y
  let t : Bᘁ ≅ E := rightDualTensorIso (Yᘁ) (Xᘁ)
  have hcoe : η_ B (Bᘁ) ≫ B ◁ t.hom = η_ B E := by
    exact Dimensions.coevaluation_rightDualIso HasRightDual.exact ExactPairing.tensor
  have hn := coevaluation_comp_rightAdjointMate r.inv
  change η_ A (Aᘁ) ≫ A ◁ (r.invᘁ) = η_ B (Bᘁ) ≫ r.inv ▷ (Bᘁ) at hn
  have hn' : η_ A (Aᘁ) = η_ B (Bᘁ) ≫ r.inv ▷ (Bᘁ) ≫ A ◁ (r.homᘁ) := by
    let k : Aᘁ ≅ Bᘁ := Dimensions.rightDualIsoMap r.symm
    letI : IsIso (r.invᘁ) := by change IsIso k.hom; infer_instance
    apply (cancel_mono (A ◁ (r.invᘁ))).1
    simp only [Category.assoc, ← whiskerLeft_comp, ← comp_rightAdjointMate, Iso.inv_hom_id,
      rightAdjointMate_id, whiskerLeft_id, Category.comp_id]
    exact hn
  rw [hn']
  have he : η_ B E ≫ B ◁ t.inv = η_ B (Bᘁ) := by
    rw [← hcoe, Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]
  rw [← he]
  dsimp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap]
  simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Left pivotal trace evaluated with the tensor dual pairing. -/
theorem leftTrace_tensor_pairing (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) (f : X ⊗ Y ⟶ X ⊗ Y) :
    (p.leftTrace f).asHom =
      η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) ≫
        ((Yᘁ) ⊗ (Xᘁ)) ◁ (((p.iso X).inv ⊗ₘ (p.iso Y).inv) ≫ f) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
  let A := X ⊗ Y
  let D := Aᘁ
  let E := (Yᘁ) ⊗ (Xᘁ)
  let r : D ≅ E := rightDualTensorIso X Y
  let q : ExactPairing A E := ExactPairing.tensor
  have hev := Dimensions.rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ A (RightRigidCategory.rightDual A)) q
  change r.inv ▷ A ≫ ε_ A D = @ExactPairing.evaluation C _ _ A E q at hev
  change η_ D (Dᘁ) ≫ (𝟙 D ⊗ₘ ((p.iso A).inv ≫ f)) ≫ ε_ A D = _
  have hp : p.iso (X ⊗ Y) = (p.iso X ⊗ᵢ p.iso Y) ≪≫ Dimensions.doubleDualTensorIso X Y :=
    Iso.ext (p.tensor X Y)
  rw [tensorDual_coevaluation, hp]
  simp only [Iso.trans_inv, tensorIso_inv, tensorHom_def, id_whiskerRight,
    whiskerLeft_id, Category.comp_id, whiskerLeft_comp, Category.assoc]
  dsimp only [A, D, E, r] at *
  simp only [Category.id_comp, ← whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  rw [← whisker_exchange_assoc, ← hev]

set_option backward.isDefEq.respectTransparency false in
/-- Closing the first tensor factor and then the remainder computes the
left pivotal trace. -/
theorem leftTrace_partialTrace [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (p : Dimensions.PivotalStructure (C := C)) (X Y : C) (f : End (X ⊗ Y)) :
    p.leftTrace (leftPartialTrace p X Y f).asHom = p.leftTrace f.asHom := by
  apply End.homEquiv.injective
  change (p.leftTrace (leftPartialTrace p X Y f).asHom).asHom = (p.leftTrace f.asHom).asHom
  rw [leftTrace_tensor_pairing]
  simp only [Dimensions.PivotalStructure.leftTrace, leftPartialTrace,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hc : η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) =
      η_ (Yᘁ) ((Yᘁ)ᘁ) ⊗≫ ((Yᘁ) ◁ η_ (Xᘁ) ((Xᘁ)ᘁ)) ▷ ((Yᘁ)ᘁ) ⊗≫ 𝟙 _ := rfl
  have he : ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      𝟙 (((Yᘁ) ⊗ (Xᘁ)) ⊗ (X ⊗ Y)) ⊗≫ ((Yᘁ) : C) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫ ε_ Y (Yᘁ) := rfl
  rw [hc, he]
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
  monoidal
  simp
  simp only [← whiskerLeft_comp_assoc]
  rw [leftUnitor_inv_naturality_assoc]
  rw [whisker_exchange_assoc (η_ (Xᘁ) ((Xᘁ)ᘁ)) (p.iso Y).inv]
  rw [associator_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [whisker_exchange_assoc (p.iso X).inv (p.iso Y).inv]

/-- In a spherical category, left partial trace computes the ordinary
pivotal trace after the remaining strand is closed. -/
theorem spherical_rightTrace_leftPartialTrace [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (p : Dimensions.PivotalStructure (C := C)) (hp : p.IsSpherical)
    (X Y : C) (f : End (X ⊗ Y)) :
    p.rightTrace (leftPartialTrace p X Y f).asHom = p.rightTrace f.asHom := by
  rw [← hp Y _, leftTrace_partialTrace, hp]

/-- A self-transparent simple with sign-valued twist has integral FP
dimension in any FP-valued spherical fusion category. -/
theorem integral_of_spherical_and_twist_sign
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical)
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj) [Simple X] (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X))
    (hsign : Dimensions.pivotalBraidedTwistScalar C p X = 1 ∨
      Dimensions.pivotalBraidedTwistScalar C p X = -1) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply integral_of_leftTrace_and_twist_sign C p hdim X hX _ hsign
  exact spherical_rightTrace_leftPartialTrace p hp X

end PropertyF.Ground.CentreCalculus
