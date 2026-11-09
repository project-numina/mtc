module
public import MTC.PropertyF.Pivotal.SlopeDefect
public import MTC.CategoryTheory.Dimensions.SimpleScalars

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! The natural comparison between a pivotal square and the canonical fourth dual. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- The natural fourth-dual map obtained by squaring a pivotal structure. -/
def pivotalSquare (X : C.Obj) : X ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ) :=
  p.iso X ≪≫ rightDualIsoMap (rightDualIsoMap (p.iso X))

/-- The pivotal square compared to the canonical braided fourth-dual map. -/
def pivotalFourthComparison (X : C.Obj) : X ≅ X :=
  pivotalSquare C p X ≪≫ (fourthDualIso X).symm

/-- The pivotal square is natural. -/
theorem pivotalSquare_natural {X Y : C.Obj} (f : X ⟶ Y) :
    f ≫ (pivotalSquare C p Y).hom = (pivotalSquare C p X).hom ≫ ((((fᘁ)ᘁ)ᘁ)ᘁ) := by
  simp only [pivotalSquare, Iso.trans_hom, rightDualIsoMap, Category.assoc]
  have h := congrArg (fun g ↦ ((gᘁ)ᘁ)) (p.naturality f)
  simp only [comp_rightAdjointMate] at h
  rw [← Category.assoc, p.naturality f, Category.assoc, h]

/-- The comparison with the canonical fourth dual is a natural automorphism. -/
theorem pivotalFourthComparison_natural {X Y : C.Obj} (f : X ⟶ Y) :
    f ≫ (pivotalFourthComparison C p Y).hom =
      (pivotalFourthComparison C p X).hom ≫ f := by
  simp only [pivotalFourthComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  apply (cancel_mono (fourthDualIso Y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, pivotalSquare_natural, Category.assoc]
  simp only [fourthDualIso_natural f, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Squaring a pivotal structure respects the canonical fourth-dual tensor comparison. -/
theorem pivotalSquare_tensor (X Y : C.Obj) :
    (pivotalSquare C p (X ⊗ Y)).hom =
      ((pivotalSquare C p X).hom ⊗ₘ (pivotalSquare C p Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  simp only [pivotalSquare, Iso.trans_hom, rightDualIsoMap, p.tensor,
    comp_rightAdjointMate, Category.assoc]
  rw [← reassoc_of% (doubleDualTensorIso_natural _ _), tensorHom_comp_tensorHom_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The pivotal/fourth-dual comparison is monoidal on tensor products. -/
theorem pivotalFourthComparison_tensor (X Y : C.Obj) :
    (pivotalFourthComparison C p (X ⊗ Y)).hom =
      ((pivotalFourthComparison C p X).hom ⊗ₘ
        (pivotalFourthComparison C p Y).hom) := by
  apply (cancel_mono (fourthDualIso (X ⊗ Y)).hom).1
  simp only [pivotalFourthComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [pivotalSquare_tensor, MTC.Center.Induction.fourthDualIso_tensor]
  have h : ((fourthDualIso X).inv ⊗ₘ (fourthDualIso Y).inv) ≫
      ((fourthDualIso X).hom ⊗ₘ (fourthDualIso Y).hom) = 𝟙 _ := by
    rw [tensorHom_comp_tensorHom]
    simp
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc, reassoc_of% h]

/-- Scalar of the pivotal/fourth-dual comparison on a simple object. -/
def pivotalFourthScalar (X : C.Obj) [Simple X] : ℂ :=
  letI : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  simpleEndScalar (k := ℂ) X (End.of (pivotalFourthComparison C p X).hom)

/-- The comparison acts as its scalar on a simple object. -/
theorem pivotalFourthComparison_simple (X : C.Obj) [Simple X] :
    (pivotalFourthComparison C p X).hom = pivotalFourthScalar C p X • 𝟙 X := by
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  exact congrArg End.asHom
    (eq_smul_one_of_algEquiv (simpleEndScalar (k := ℂ) X)
      (End.of (pivotalFourthComparison C p X).hom))

/-- A nonzero morphism into a tensor product forces the comparison scalars
on its three simple objects to multiply. -/
theorem pivotalFourthScalar_tensor_of_hom (X Y Z : C.Obj)
    [Simple X] [Simple Y] [Simple Z] (f : Z ⟶ X ⊗ Y) (hf : f ≠ 0) :
    pivotalFourthScalar C p Z = pivotalFourthScalar C p X * pivotalFourthScalar C p Y := by
  have h := pivotalFourthComparison_natural C p f
  rw [pivotalFourthComparison_tensor, pivotalFourthComparison_simple,
    pivotalFourthComparison_simple, pivotalFourthComparison_simple] at h
  simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul,
    MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp,
    smul_smul, whiskerLeft_id, id_whiskerRight, Category.comp_id, Category.id_comp] at h
  exact (smul_left_injective ℂ hf (by simpa [mul_comm] using h)).symm

end MTC.PropertyF.Pivotal
end
