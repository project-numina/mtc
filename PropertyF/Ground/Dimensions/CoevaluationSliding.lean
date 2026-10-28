module
public import PropertyF.Ground.Dimensions.DefectNaturality

/-! # Coevaluation sliding and reciprocity

Sliding tensor defects through coevaluations yields reciprocity for trace matrices.

## Main results

* `tensorLeftHomLinearEquiv_postcomp`: describes composition under Frobenius reciprocity.
* `enoTraceMatrix_reciprocity_of_coevaluation_sliding`: derives trace reciprocity from coevaluation sliding.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]

theorem tensorLeftHomLinearEquiv_postcomp (X Y Y' Z W : D) [ExactPairing Y Y']
    (f : Y' ⊗ X ⟶ Z) (g : Z ⟶ W) :
    tensorLeftHomLinearEquiv X Y Y' W (f ≫ g) =
      tensorLeftHomLinearEquiv X Y Y' Z f ≫ Y ◁ g :=
  by simp [tensorLeftHomLinearEquiv, tensorLeftHomEquiv, whiskerLeft_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The Frobenius defect equation reduces to its value on the identity map. -/
theorem enoTraceMatrix_reciprocity_of_coevaluation_defect
    (hunit : ∀ i k,
      let X := simples C i
      let K := simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (rootTensorDefect C X K).hom =
        rootDualSign C i • (tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (𝟙 (X ⊗ K)) ≫
          (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)) :
    ENOTraceMatrixReciprocity C := by
  apply enoTraceMatrix_reciprocity_of_dual_frobenius_defect C
  intro i j k g
  let X := simples C i
  let K := simples C k
  let J := simples C j
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  have hpost := tensorLeftHomLinearEquiv_postcomp K (Xᘁ) X (X ⊗ K) J
    (rootTensorDefect C X K).hom g
  have hpost' := tensorLeftHomLinearEquiv_postcomp K (Xᘁ) X (X ⊗ K) J
    (𝟙 (X ⊗ K)) g
  have hn := rootTensorDefect_natural C (𝟙 (Xᘁ)) g
  simp only [id_tensorHom] at hn
  simp only [Category.id_comp] at hpost'
  rw [hpost, hunit i k, Linear.smul_comp, Category.assoc, ← hn, ← Category.assoc, ← hpost']
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The ENO reciprocity identity only needs the defect to slide through the
coevaluation of the swapped dual pairing. -/
theorem enoTraceMatrix_reciprocity_of_coevaluation_sliding
    (hslide : ∀ i k,
      let X := simples C i
      let K := simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
        (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
      η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
        rootDualSign C i • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)) :
    ENOTraceMatrixReciprocity C := by
  apply enoTraceMatrix_reciprocity_of_coevaluation_defect C
  intro i k
  let X := simples C i
  let K := simples C k
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  change ((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
      (Xᘁ) ◁ (rootTensorDefect C X K).hom) =
    rootDualSign C i • (((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
      (Xᘁ) ◁ 𝟙 (X ⊗ K)) ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)
  simpa only [whiskerLeft_id, Category.comp_id, Category.assoc] using hslide i k
end PropertyF.Ground.Dimensions

end
