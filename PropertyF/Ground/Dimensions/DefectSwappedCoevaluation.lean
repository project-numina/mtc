module
public import PropertyF.Ground.Dimensions.DefectCoevaluation
public import PropertyF.Ground.Dimensions.DefectNaturality
public import PropertyF.Ground.Dimensions.RootDualLabel

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Coevaluation is transported by an isomorphism and its inverse right dual. -/
theorem coevaluation_iso_map {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] {X Y : C} (a : X ≅ Y) :
    η_ X (Xᘁ) ≫ (a.hom ⊗ₘ (a.invᘁ)) = η_ Y (Yᘁ) := by
  simp only [tensorHom_def]
  have h := coevaluation_comp_rightAdjointMate a.inv
  calc
    _ = η_ X (Xᘁ) ≫ X ◁ (a.invᘁ) ≫ a.hom ▷ (Yᘁ) := by
      simpa only [Category.assoc] using
        congrArg (fun z => η_ X (Xᘁ) ≫ z) (whisker_exchange a.hom (a.invᘁ)).symm
    _ = η_ Y (Yᘁ) ≫ a.inv ▷ (Yᘁ) ≫ a.hom ▷ (Yᘁ) := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ a.hom ▷ (Yᘁ)) h
    _ = _ := by simp only [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The cup eigenvalue is invariant under changing the simple representative. -/
theorem rootTensorDefect_coevaluation_of_iso (C : Ground.BraidedFusionCategory.{v,u})
    {X : C.Obj} (i : Fin (Ground.rank C)) (a : X ≅ Ground.simples C i) :
    η_ X (Xᘁ) ≫ (rootTensorDefect C X (Xᘁ)).hom =
      (rootDimension C (Ground.unitIndex C) * rootDualSign C i) • η_ X (Xᘁ) := by
  let Y := Ground.simples C i
  let b := (rightDualIsoMap a).symm
  let d := a ⊗ᵢ b
  have hc : η_ X (Xᘁ) ≫ d.hom = η_ Y (Yᘁ) := coevaluation_iso_map a
  have hn := rootTensorDefect_natural C a.hom b.hom
  change d.hom ≫ (rootTensorDefect C Y (Yᘁ)).hom =
    (rootTensorDefect C X (Xᘁ)).hom ≫ d.hom at hn
  apply (cancel_mono d.hom).1
  calc
    _ = η_ X (Xᘁ) ≫ (d.hom ≫ (rootTensorDefect C Y (Yᘁ)).hom) := by
      rw [hn, Category.assoc]
    _ = η_ Y (Yᘁ) ≫ (rootTensorDefect C Y (Yᘁ)).hom := by rw [← Category.assoc, hc]
    _ = _ := by rw [rootTensorDefect_coevaluation, ← hc, Linear.smul_comp]
set_option backward.isDefEq.respectTransparency false in
/-- The root defect has the same eigenvalue on the braided-swapped cup. -/
theorem rootTensorDefect_swapped_coevaluation (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    let X := Ground.simples C i
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    η_ (Xᘁ) X ≫ (rootTensorDefect C (Xᘁ) X).hom =
      (rootDimension C (Ground.unitIndex C) * rootDualSign C i) • η_ (Xᘁ) X := by
  let X := Ground.simples C i
  let A := Xᘁ
  let Q := (Xᘁ)ᘁ
  let p : ExactPairing A X := BraidedCategory.exactPairing_swap X A
  let q : ExactPairing A Q := HasRightDual.exact
  let : ExactPairing A X := p
  let : ExactPairing A Q := q
  let r : X ≅ Q := rightDualIso p q
  have hc := coevaluation_rightDualIso p q
  change η_ A X ≫ A ◁ r.hom = η_ A Q at hc
  have hn := rootTensorDefect_natural C (𝟙 A) r.hom
  simp only [id_tensorHom] at hn
  have he := rootTensorDefect_coevaluation_of_iso C (Ground.dualIndex C i) (rightDualLabelIso C i)
  change η_ A Q ≫ (rootTensorDefect C A Q).hom = _ at he
  rw [rootDualSign_dual] at he
  apply (cancel_mono (A ◁ r.hom)).1
  calc
    _ = η_ A X ≫ ((A ◁ r.hom) ≫ (rootTensorDefect C A Q).hom) := by
      rw [hn, Category.assoc]
    _ = η_ A Q ≫ (rootTensorDefect C A Q).hom := by rw [← Category.assoc, hc]
    _ = _ := by rw [he, ← hc, Linear.smul_comp]
end PropertyF.Ground.Dimensions
