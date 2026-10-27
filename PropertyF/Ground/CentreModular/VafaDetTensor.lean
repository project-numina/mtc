module
public import PropertyF.Ground.CentreModular.VafaDeterminant

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- FP determinants are invariant under actual categorical conjugation. -/
theorem fpDeterminant_conjugate (C : BraidedFusionCategory.{v,u})
    {X Y : C.Obj} (e : X ≅ Y) (a : X ≅ X) :
    fpDeterminant C Y (e.symm ≪≫ a ≪≫ e) = fpDeterminant C X a := by
  unfold fpDeterminant
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  let E := CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C i)) e
  have h : simpleHomAction C Y i (e.symm ≪≫ a ≪≫ e) =
      ((E.symm.trans (simpleHomAction C X i a)).trans E) := by
    ext f
    simp [simpleHomAction, E, CategoryTheory.Linear.homCongr_apply,
      CategoryTheory.Linear.homCongr_symm_apply, Category.assoc]
  rw [h, LinearEquiv.det_conj]

/-- Tensoring a scalar automorphism preserves the scalar action. -/
theorem tensor_scalarIso (C : BraidedFusionCategory.{v,u})
    (X Y : C.Obj) (z : ℂˣ) :
    Iso.refl X ⊗ᵢ scalarIso C Y z = scalarIso C (X ⊗ Y) z := by
  apply Iso.ext
  simp [scalarIso, tensorHom_def]

/-- The tensor-product determinant rule when the second automorphism is scalar. -/
theorem fpDeterminant_tensor_scalar (C : BraidedFusionCategory.{v,u})
    (X Y : C.Obj) (z : ℂˣ) :
    fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ scalarIso C Y z) =
      fpDimension C X • fpDeterminant C Y (scalarIso C Y z) := by
  rw [tensor_scalarIso, fpDeterminant_scalar, fpDeterminant_scalar, fpDimension_tensor, mul_smul]

/-- Every actual automorphism of a simple representative is scalar. -/
theorem simple_iso_eq_scalarIso (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) (a : simples C i ≅ simples C i) :
    ∃ z : ℂˣ, a = scalarIso C (simples C i) z := by
  let : Simple (simples C i) := simples_simple C i
  let : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  obtain ⟨z, hz⟩ := endomorphism_simple_eq_smul_id ℂ a.hom
  have hne : z ≠ 0 := by
    intro h
    have ha : a.hom = 0 := by simpa [h] using hz.symm
    have hh := a.hom_inv_id
    simp [ha] at hh
    exact id_nonzero _ hh.symm
  refine ⟨Units.mk0 z hne, ?_⟩
  apply Iso.ext
  exact hz.symm

/-- The tensor-product determinant rule holds for every simple-object
automorphism, without extra hypotheses. -/
theorem fpDeterminant_tensor_simple (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) (i : Fin (rank C)) (a : simples C i ≅ simples C i) :
    fpDeterminant C (X ⊗ simples C i) (Iso.refl X ⊗ᵢ a) =
      fpDimension C X • fpDeterminant C (simples C i) a := by
  obtain ⟨z, rfl⟩ := simple_iso_eq_scalarIso C i a
  exact fpDeterminant_tensor_scalar C X (simples C i) z

end PropertyF.Ground.CentreModular
