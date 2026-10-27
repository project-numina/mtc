module
public import PropertyF.Ground.Dimensions.DualCoherence

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
  have he := rightDualIso_inv_evaluation q1 q2
  dsimp only [PivotalStructure.rightTrace]
  rw [p.tensor X Y]
  have hr : @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      ((u ≫ s.inv) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Yᘁ) ⊗ (Xᘁ))ᘁ) q1 =
      @ExactPairing.coevaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) p2 ≫
      (u ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
        @ExactPairing.evaluation C _ _ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) q2 := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight, Category.assoc]
    rw [he]
  have h := ht.trans hr
  simpa only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap,
    Category.assoc, rightDualTensorIso, r, s, u, p1, p2, q1, q2] using h

end PropertyF.Ground.Dimensions
