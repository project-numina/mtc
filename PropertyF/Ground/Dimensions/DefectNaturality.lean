module
public import PropertyF.Ground.Dimensions.RootDualLabel

/-! # Naturality of tensor defects

Naturality of the root tensor isomorphism and defect yields trace reciprocity identities.

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
  change (f ⊗ₘ g) ≫
      ((((fourthDualRootNaturalIso C).app X').hom ⊗ₘ ((fourthDualRootNaturalIso C).app Y').hom) ≫
        (doubleDualTensorIso X' Y').hom) =
    ((((fourthDualRootNaturalIso C).app X).hom ⊗ₘ ((fourthDualRootNaturalIso C).app Y).hom) ≫
        (doubleDualTensorIso X Y).hom) ≫ (((f ⊗ₘ g)ᘁ)ᘁ)
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

/-- The dual-label choice can be removed from the Frobenius defect equation. -/
theorem trace_reciprocity_of_dual_defect
    (hraw : ∀ i j k (g : simples C i ⊗ simples C k ⟶ simples C j),
      letI : ExactPairing ((simples C i)ᘁ) (simples C i) :=
        BraidedCategory.exactPairing_swap _ _
      tensorLeftHomLinearEquiv (simples C k) ((simples C i)ᘁ)
          (simples C i) (simples C j)
          ((rootTensorDefect C (simples C i) (simples C k)).hom ≫ g) =
        rootDualSign C i • (tensorLeftHomLinearEquiv (simples C k)
            ((simples C i)ᘁ) (simples C i) (simples C j) g ≫
          (rootTensorDefect C ((simples C i)ᘁ) (simples C j)).hom)) :
    ENOTraceMatrixReciprocity C := by
  apply trace_reciprocity_of_frobenius_defect C
  intro i j k g
  let : ExactPairing ((simples C i)ᘁ) (simples C i) :=
    BraidedCategory.exactPairing_swap _ _
  have hn := rootTensorDefect_natural C (rightDualLabelIso C i).hom (𝟙 (simples C j))
  simp only [enoFrobeniusEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, tensorIso_hom] 
  rw [(hraw i j k g)]
  simp only [Linear.smul_comp, Category.assoc, ← hn]

end PropertyF.Ground.Dimensions
