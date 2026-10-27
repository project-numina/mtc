module
public import PropertyF.Ground.Dimensions.FourthTensorUnit
public import PropertyF.Ground.Dimensions.CoevaluationSliding

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- A signed scalar tensor defect forces the fourth-dual tensor law. -/
theorem fourthDualIso_tensor_of_signed_defect (C : Ground.BraidedFusionCategory.{v,u})
    (X Y : C.Obj) (z : ℂ) (hz : z * z = 1)
    (hd : (rootTensorDefect C X Y).hom = z • 𝟙 (X ⊗ Y)) :
    (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  let T := rootTensorIso C X Y
  let A := (fourthDualRootNaturalIso C).app (X ⊗ Y)
  have hcomp : (z • 𝟙 (X ⊗ Y)) ≫ T.hom = A.hom := by
    rw [← hd]
    change (A.hom ≫ T.inv) ≫ T.hom = A.hom
    simp only [doubleDualFunctor, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcomp' : z • T.hom = A.hom := by simpa [Linear.smul_comp] using hcomp
  have ht : T.hom = z • A.hom := by
    have hm := congrArg (fun f => z • f) hcomp'
    simp only [smul_smul, hz, one_smul] at hm
    exact hm
  have hsq : T.hom ≫ ((T.homᘁ)ᘁ) = (fourthDualIso C (X ⊗ Y)).hom := by
    rw [ht]
    simp only [rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
      hz, one_smul]
    exact congrArg (fun n => (n.app (X ⊗ Y)).hom) (fourthDualRootNaturalSquare_eq C)
  exact hsq.symm.trans (rootTensor_square_eq_fourthDual_tensor C X Y)

/-- The fourth-dual tensor law holds when the left factor is the chosen unit
simple representative. -/
theorem fourthDualIso_tensor_unitLabel_left (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (fourthDualIso C (Ground.simples C (Ground.unitIndex C) ⊗ X)).hom =
      ((fourthDualIso C (Ground.simples C (Ground.unitIndex C))).hom ⊗ₘ (fourthDualIso C X).hom) ≫
        (doubleDualTensorIso (((Ground.simples C (Ground.unitIndex C))ᘁ)ᘁ) ((Xᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C (Ground.unitIndex C)) X).homᘁ)ᘁ) :=
  fourthDualIso_tensor_of_signed_defect C _ _ (rootDimension C (Ground.unitIndex C))
    (rootDimension_unit_sq C) (rootTensorDefect_unitLabel_left C X)

/-- The fourth-dual tensor law holds when the right factor is the chosen unit
simple representative. -/
theorem fourthDualIso_tensor_unitLabel_right (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (fourthDualIso C (X ⊗ Ground.simples C (Ground.unitIndex C))).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C (Ground.simples C (Ground.unitIndex C))).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) (((Ground.simples C (Ground.unitIndex C))ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X (Ground.simples C (Ground.unitIndex C))).homᘁ)ᘁ) :=
  fourthDualIso_tensor_of_signed_defect C _ _ (rootDimension C (Ground.unitIndex C))
    (rootDimension_unit_sq C) (rootTensorDefect_unitLabel_right C X)
/-- The unit label is fixed by the simple-dual involution. -/
theorem dualIndex_unit (C : Ground.BraidedFusionCategory.{v,u}) :
    Ground.dualIndex C (Ground.unitIndex C) = Ground.unitIndex C := by
  have h := Ground.fusionCoeff_dual_unit C (Ground.unitIndex C)
  rw [Ground.fusionCoeff_unit] at h
  by_cases he : Ground.unitIndex C = Ground.dualIndex C (Ground.unitIndex C)
  · exact he.symm
  · simp [he] at h

/-- The root tensor defect is the unit sign when its left factor is the right
dual of the chosen unit representative. -/
theorem rootTensorDefect_unitLabelDual_left (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rootTensorDefect C ((Ground.simples C (Ground.unitIndex C))ᘁ) X).hom =
      rootDimension C (Ground.unitIndex C) • 𝟙 (((Ground.simples C (Ground.unitIndex C))ᘁ) ⊗ X) := by
  let e : ((Ground.simples C (Ground.unitIndex C))ᘁ) ≅
      Ground.simples C (Ground.unitIndex C) := by
    simpa only [dualIndex_unit] using rightDualLabelIso C (Ground.unitIndex C)
  let E := e ⊗ᵢ Iso.refl X
  apply (cancel_mono E.hom).1
  have h := rootTensorDefect_natural C e.hom (𝟙 X)
  change E.hom ≫ (rootTensorDefect C (Ground.simples C (Ground.unitIndex C)) X).hom =
    (rootTensorDefect C ((Ground.simples C (Ground.unitIndex C))ᘁ) X).hom ≫ E.hom at h
  rw [← h, rootTensorDefect_unitLabel_left]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- The ENO coevaluation slide holds for the unit simple label. -/
theorem coevaluation_slide_unitLabel (C : Ground.BraidedFusionCategory.{v,u}) (k : Fin (Ground.rank C)) :
    let X := Ground.simples C (Ground.unitIndex C)
    let K := Ground.simples C k
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
      (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
    η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
      rootDualSign C (Ground.unitIndex C) • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom) := by
  let X := Ground.simples C (Ground.unitIndex C)
  let K := Ground.simples C k
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  dsimp only
  rw [rootTensorDefect_unitLabel_left, rootTensorDefect_unitLabelDual_left, rootDualSign_unit]
  simp only [MonoidalLinear.whiskerLeft_smul, whiskerLeft_id, Linear.comp_smul,
    Category.comp_id, one_smul]
/-- Positive spherical existence reduces to non-unit fourth-dual and
coevaluation-slide cases. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_nonunit_coherences
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ i j : Fin (Ground.rank C), i ≠ Ground.unitIndex C → j ≠ Ground.unitIndex C →
      (fourthDualIso C (Ground.simples C i ⊗ Ground.simples C j)).hom =
      ((fourthDualIso C (Ground.simples C i)).hom ⊗ₘ (fourthDualIso C (Ground.simples C j)).hom) ≫
        (doubleDualTensorIso (((Ground.simples C i)ᘁ)ᘁ) (((Ground.simples C j)ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C i) (Ground.simples C j)).homᘁ)ᘁ))
    (hslide : ∀ i k, i ≠ Ground.unitIndex C →
      let X := Ground.simples C i
      let K := Ground.simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
        (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
      η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
        rootDualSign C i • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom))
    (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  apply eno_pseudoUnitary_yields_positive_spherical_of_simple_fourth_and_reciprocity C _ _ hpu
  · intro i j
    by_cases hi : i = Ground.unitIndex C
    · subst i
      exact fourthDualIso_tensor_unitLabel_left C (Ground.simples C j)
    · by_cases hj : j = Ground.unitIndex C
      · subst j
        exact fourthDualIso_tensor_unitLabel_right C (Ground.simples C i)
      · exact hfourth i j hi hj
  · apply enoTraceMatrix_reciprocity_of_coevaluation_sliding C
    intro i k
    by_cases hi : i = Ground.unitIndex C
    · subst i
      exact coevaluation_slide_unitLabel C k
    · exact hslide i k hi
/-- Every rank-one braided fusion category is pseudo-unitary. -/
theorem rankOne_pseudoUnitary (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] : Ground.PseudoUnitary C := by
  have hs (f : Fin (Ground.rank C) → ℂ) : ∑ i, f i = f (Ground.unitIndex C) := by
    apply Finset.sum_eq_single (Ground.unitIndex C)
    · intro i _ hi
      exact (hi (Subsingleton.elim i (Ground.unitIndex C))).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hf (f : Fin (Ground.rank C) → ℝ) : ∑ i, f i = f (Ground.unitIndex C) := by
    apply Finset.sum_eq_single (Ground.unitIndex C)
    · intro i _ hi
      exact (hi (Subsingleton.elim i (Ground.unitIndex C))).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hnorm : Ground.squaredNorm C (Ground.simples C (Ground.unitIndex C)) = 1 := by
    let : Simple (Ground.simples C (Ground.unitIndex C)) := Ground.simples_simple C _
    let : Simple (𝟙_ C.Obj) := Ground.IsFusionCategory.unit_simple
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [target_squaredNorm_iso C e, target_squaredNorm_unit]
  change (∑ i, Ground.squaredNorm C (Ground.simples C i)) =
    ((∑ i, Ground.fpSimple C i ^ 2 : ℝ) : ℂ)
  rw [hs, hf, hnorm, Ground.fpSimple_unit]
  norm_num

/-- Every rank-one braided fusion category has its positive spherical structure. -/
theorem rankOne_positive_spherical (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  apply eno_pseudoUnitary_yields_positive_spherical_of_nonunit_coherences C _ _ (rankOne_pseudoUnitary C)
  · intro i j hi _
    exact (hi (Subsingleton.elim i (Ground.unitIndex C))).elim
  · intro i k hi
    exact (hi (Subsingleton.elim i (Ground.unitIndex C))).elim
end PropertyF.Ground.Dimensions
