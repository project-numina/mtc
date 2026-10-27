module
public import PropertyF.Ground.Dimensions.DefectNaturality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]

theorem tensorLeftHomLinearEquiv_postcomp (X Y Y' Z W : D) [ExactPairing Y Y']
    (f : Y' ⊗ X ⟶ Z) (g : Z ⟶ W) :
    Ground.tensorLeftHomLinearEquiv X Y Y' W (f ≫ g) =
      Ground.tensorLeftHomLinearEquiv X Y Y' Z f ≫ Y ◁ g := by
  simp [Ground.tensorLeftHomLinearEquiv, tensorLeftHomEquiv, whiskerLeft_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The Frobenius defect equation reduces to its value on the identity map. -/
theorem enoTraceMatrix_reciprocity_of_coevaluation_defect
    (C : Ground.BraidedFusionCategory.{v,u})
    (hunit : ∀ i k,
      let X := Ground.simples C i
      let K := Ground.simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      Ground.tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (rootTensorDefect C X K).hom =
        rootDualSign C i • (Ground.tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (𝟙 (X ⊗ K)) ≫
          (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j := by
  apply enoTraceMatrix_reciprocity_of_rightDual_frobenius_defect C
  intro i j k g
  let X := Ground.simples C i
  let K := Ground.simples C k
  let J := Ground.simples C j
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  have hpost := tensorLeftHomLinearEquiv_postcomp K (Xᘁ) X (X ⊗ K) J
    (rootTensorDefect C X K).hom g
  have hpost' := tensorLeftHomLinearEquiv_postcomp K (Xᘁ) X (X ⊗ K) J
    (𝟙 (X ⊗ K)) g
  have hn := rootTensorDefect_natural C (𝟙 (Xᘁ)) g
  simp only [id_tensorHom] at hn
  simp only [Category.id_comp] at hpost'
  rw [hpost, hunit i k, Linear.smul_comp, Category.assoc, ← hn, ← Category.assoc, ← hpost']
/-- Positive spherical existence from the remaining fourth-dual and
coevaluation identities. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_coevaluation
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ i j : Fin (Ground.rank C),
      (fourthDualIso C (Ground.simples C i ⊗ Ground.simples C j)).hom =
      ((fourthDualIso C (Ground.simples C i)).hom ⊗ₘ (fourthDualIso C (Ground.simples C j)).hom) ≫
        (doubleDualTensorIso (((Ground.simples C i)ᘁ)ᘁ) (((Ground.simples C j)ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C i) (Ground.simples C j)).homᘁ)ᘁ))
    (hunit : ∀ i k,
      let X := Ground.simples C i
      let K := Ground.simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      Ground.tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (rootTensorDefect C X K).hom =
        rootDualSign C i • (Ground.tensorLeftHomLinearEquiv K (Xᘁ) X (X ⊗ K) (𝟙 (X ⊗ K)) ≫
          (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom))
    (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) :=
  eno_pseudoUnitary_yields_positive_spherical_of_simple_fourth_and_reciprocity C hfourth
    (enoTraceMatrix_reciprocity_of_coevaluation_defect C hunit) hpu

end PropertyF.Ground.Dimensions
