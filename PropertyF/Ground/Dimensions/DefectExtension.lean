module
public import PropertyF.Ground.Dimensions.DefectSliding
public import PropertyF.Ground.Dimensions.TensorExtension
public import PropertyF.Ground.Dimensions.RankOneSpherical

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- Involutivity on simple pairs extends to all object pairs by semisimple decomposition. -/
theorem rootTensorDefect_involution_extension (C : Ground.BraidedFusionCategory.{v,u})
    (hsimple : ∀ i j, (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom ≫
      (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom =
        𝟙 (Ground.simples C i ⊗ Ground.simples C j)) (X Y : C.Obj) :
    (rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom = 𝟙 (X ⊗ Y) := by
  classical
  let ex := simpleDecomposition C X
  let ey := simpleDecomposition C Y
  let V := simplePiecesObject C X
  let W := simplePiecesObject C Y
  apply (cancel_epi (ex.symm ⊗ᵢ ey.symm).hom).1
  apply tensorBiproduct_hom_ext C V W
  intro i j
  let sx : Ground.simples C i.1 ⟶ X := biproduct.ι V i ≫ ex.inv
  let sy : Ground.simples C j.1 ⟶ Y := biproduct.ι W j ≫ ey.inv
  have hn := rootTensorDefect_natural C sx sy
  have hh : (sx ⊗ₘ sy) ≫ ((rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom) =
      (sx ⊗ₘ sy) ≫ 𝟙 (X ⊗ Y) := by
    rw [← Category.assoc, hn, Category.assoc, hn, ← Category.assoc, hsimple, Category.id_comp, Category.comp_id]
  simpa [sx, sy, ex, ey, V, W, tensorIso_hom, tensorHom_comp_tensorHom,
    Category.assoc] using hh
/-- The fourth-dual tensor law on simple pairs implies ENO trace reciprocity. -/
theorem enoTraceMatrix_reciprocity_of_simple_fourthDual_tensor
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ i j : Fin (Ground.rank C),
      (fourthDualIso C (Ground.simples C i ⊗ Ground.simples C j)).hom =
      ((fourthDualIso C (Ground.simples C i)).hom ⊗ₘ (fourthDualIso C (Ground.simples C j)).hom) ≫
        (doubleDualTensorIso (((Ground.simples C i)ᘁ)ᘁ) (((Ground.simples C j)ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C i) (Ground.simples C j)).homᘁ)ᘁ)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k = rootDualSign C i * enoTraceMatrix C i k j := by
  have hinv : ∀ X Y : C.Obj, (rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom = 𝟙 (X ⊗ Y) := by
    apply rootTensorDefect_involution_extension C
    intro i j
    apply rootTensorDefect_involution_of_tensor_square C
    rw [rootTensor_square_eq_fourthDual_tensor, ← hfourth]
  apply enoTraceMatrix_reciprocity_of_coevaluation_sliding C
  intro i k
  exact rootTensorDefect_slide_of_involution C i (Ground.simples C k) (hinv _ _)

/-- The fourth-dual law on non-unit simple pairs suffices for the canonical pseudo-unitary spherical structure. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_nonunit_fourthDual_tensor
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ i j : Fin (Ground.rank C), i ≠ Ground.unitIndex C → j ≠ Ground.unitIndex C →
      (fourthDualIso C (Ground.simples C i ⊗ Ground.simples C j)).hom =
      ((fourthDualIso C (Ground.simples C i)).hom ⊗ₘ (fourthDualIso C (Ground.simples C j)).hom) ≫
        (doubleDualTensorIso (((Ground.simples C i)ᘁ)ᘁ) (((Ground.simples C j)ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C i) (Ground.simples C j)).homᘁ)ᘁ))
    (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  have hsimple : ∀ i j : Fin (Ground.rank C),
      (fourthDualIso C (Ground.simples C i ⊗ Ground.simples C j)).hom =
      ((fourthDualIso C (Ground.simples C i)).hom ⊗ₘ (fourthDualIso C (Ground.simples C j)).hom) ≫
        (doubleDualTensorIso (((Ground.simples C i)ᘁ)ᘁ) (((Ground.simples C j)ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C i) (Ground.simples C j)).homᘁ)ᘁ) := by
    intro i j
    by_cases hi : i = Ground.unitIndex C
    · subst i
      exact fourthDualIso_tensor_unitLabel_left C (Ground.simples C j)
    · by_cases hj : j = Ground.unitIndex C
      · subst j
        exact fourthDualIso_tensor_unitLabel_right C (Ground.simples C i)
      · exact hfourth i j hi hj
  exact eno_pseudoUnitary_yields_positive_spherical_of_simple_fourth_and_reciprocity C hsimple
    (enoTraceMatrix_reciprocity_of_simple_fourthDual_tensor C hsimple) hpu
end PropertyF.Ground.Dimensions
