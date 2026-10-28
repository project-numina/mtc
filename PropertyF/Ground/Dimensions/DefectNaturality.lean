module
public import PropertyF.Ground.Dimensions.RootDualLabel

/-! # Tensor-defect naturality and coevaluation sliding

Naturality of the root tensor isomorphism and sliding through coevaluation yield trace reciprocity.

## Main results

* `rootTensorIso_natural`: proves naturality of the tensor comparison for fourth-dual roots.
* `rootTensorDefect_natural`: derives naturality of its defect.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The tensor of natural-root components is natural. -/
theorem rootTensorIso_natural
    {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (rootTensorIso C X' Y').hom =
      (rootTensorIso C X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) := by
  have hf : f ≫ ((fourthDualRootNaturalIso C).app X').hom =
      ((fourthDualRootNaturalIso C).app X).hom ≫ ((fᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality f
  have hg : g ≫ ((fourthDualRootNaturalIso C).app Y').hom =
      ((fourthDualRootNaturalIso C).app Y).hom ≫ ((gᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality g
  simp only [rootTensorIso, Iso.trans_hom, tensorIso_hom]
  rw [Category.assoc, ← doubleDualTensorIso_natural, ← Category.assoc,
    ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hf, hg]

/-- The multiplicativity defect is natural in both variables. -/
theorem rootTensorDefect_natural
    {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (rootTensorDefect C X' Y').hom =
      (rootTensorDefect C X Y).hom ≫ (f ⊗ₘ g) := by
  have hni : (((f ⊗ₘ g)ᘁ)ᘁ) ≫ (rootTensorIso C X' Y').inv =
      (rootTensorIso C X Y).inv ≫ (f ⊗ₘ g) :=
    iso_inv_naturality_of_hom (rootTensorIso_natural C f g)
  have ha : (f ⊗ₘ g) ≫ ((fourthDualRootNaturalIso C).app (X' ⊗ Y')).hom =
      ((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (f ⊗ₘ g)
  change (f ⊗ₘ g) ≫ (((fourthDualRootNaturalIso C).app (X' ⊗ Y')).hom ≫
        (rootTensorIso C X' Y').inv) =
      (((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ (rootTensorIso C X Y).inv) ≫ (f ⊗ₘ g)
  dsimp only [doubleDualFunctor] at ha ⊢
  rw [← Category.assoc, ha, Category.assoc, hni, Category.assoc]


end PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]

theorem tensorLeftHomLinearEquiv_postcomp {X Y' Z W : D} (Y : D) [ExactPairing Y Y']
    (f : Y' ⊗ X ⟶ Z) (g : Z ⟶ W) :
    tensorLeftHomLinearEquiv X Y Y' W (f ≫ g) =
      tensorLeftHomLinearEquiv X Y Y' Z f ≫ Y ◁ g :=
  by simp [tensorLeftHomLinearEquiv, tensorLeftHomEquiv, whiskerLeft_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The Frobenius defect equation reduces to its value on the identity map. -/
theorem trace_reciprocity_of_coeval_defect
    (hunit : ∀ i k,
      let X := simples C i
      let K := simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (rootTensorDefect C X K).hom =
        rootDualSign C i • (tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (𝟙 (X ⊗ K)) ≫
          (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)) :
    ENOTraceMatrixReciprocity C := by
  apply trace_reciprocity_of_frobenius_defect C
  intro i j k g
  let X := simples C i
  let K := simples C k
  let J := simples C j
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  have hpost := tensorLeftHomLinearEquiv_postcomp (Xᘁ) (rootTensorDefect C X K).hom g
  have hpost' := tensorLeftHomLinearEquiv_postcomp (Xᘁ) (𝟙 (X ⊗ K)) g
  have hn := rootTensorDefect_natural C (𝟙 (Xᘁ)) g
  simp only [id_tensorHom] at hn
  simp only [Category.id_comp] at hpost'
  have hnlabel := rootTensorDefect_natural C (rightDualLabelIso C i).hom (𝟙 J)
  simp only [enoFrobeniusEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, tensorIso_hom]
  rw [hpost, hunit i k, Linear.smul_comp, Category.assoc, ← hn, ← Category.assoc, ← hpost']
  dsimp only [X, K, J] at hnlabel ⊢
  simp only [Linear.smul_comp, Category.assoc, ← hnlabel]
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The signed tensor defect slides across the coevaluation of a simple object. -/
abbrev RootTensorDefectSlide (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) (K : C.Obj) : Prop :=
  let X := simples C i
  letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
    (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
  η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
    rootDualSign C i • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The ENO reciprocity identity only needs the defect to slide through the
coevaluation of the swapped dual pairing. -/
theorem trace_reciprocity_of_coevaluation
    (hslide : ∀ i k, RootTensorDefectSlide C i (simples C k)) :
    ENOTraceMatrixReciprocity C := by
  apply trace_reciprocity_of_coeval_defect C
  intro i k
  let X := simples C i
  let K := simples C k
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  change ((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
      (Xᘁ) ◁ (rootTensorDefect C X K).hom) =
    rootDualSign C i • (((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
      (Xᘁ) ◁ 𝟙 (X ⊗ K)) ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)
  simpa only [RootTensorDefectSlide, whiskerLeft_id, Category.comp_id, Category.assoc] using hslide i k
end PropertyF.Ground.Dimensions

end
