module
public import PropertyF.Ground.CentreModular.VafaTorsion
public import Mathlib.LinearAlgebra.Determinant
public import PropertyF.Ground.Fusion.ObjectDimension

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- The linear automorphism induced on Hom from a chosen simple. -/
def simpleHomAction (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
    (i : Fin (rank C)) (a : X ≅ X) :
    (simples C i ⟶ X) ≃ₗ[ℂ] (simples C i ⟶ X) :=
  CategoryTheory.Linear.homCongr ℂ (Iso.refl _) a

theorem simpleHomAction_trans (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
    (i : Fin (rank C)) (a b : X ≅ X) :
    simpleHomAction C X i (a ≪≫ b) =
      (simpleHomAction C X i a).trans (simpleHomAction C X i b) := by
  ext f
  simp [simpleHomAction, CategoryTheory.Linear.homCongr_apply, Category.assoc]

/-- The actual FP-weighted categorical determinant of an automorphism,
valued in a real vector space that detects torsion. -/
def fpDeterminant (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (a : X ≅ X) :
    vafaUnitSpace :=
  ∑ i, fpSimple C i • vafaUnitClass (simpleHomAction C X i a).det

/-- FP determinants turn composition into addition. -/
theorem fpDeterminant_trans (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
    (a b : X ≅ X) : fpDeterminant C X (a ≪≫ b) =
      fpDeterminant C X a + fpDeterminant C X b := by
  unfold fpDeterminant
  simp_rw [simpleHomAction_trans, LinearEquiv.det_trans, vafaUnitClass_mul, smul_add]
  rw [Finset.sum_add_distrib]
  rw [add_comm]

/-- The actual scalar automorphism of an object. -/
def scalarIso (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (z : ℂˣ) : X ≅ X where
  hom := (z : ℂ) • 𝟙 X
  inv := ((z⁻¹ : ℂˣ) : ℂ) • 𝟙 X
  hom_inv_id := by simp [Linear.comp_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_smul, smul_smul]

/-- On a scalar map, each Hom-space determinant is the corresponding power. -/
theorem simpleHomAction_det_scalar (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
    (i : Fin (rank C)) (z : ℂˣ) :
    (simpleHomAction C X i (scalarIso C X z)).det =
      z ^ Module.finrank ℂ (simples C i ⟶ X) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det _ = (z : ℂ) ^ _
  have h : (simpleHomAction C X i (scalarIso C X z)).toLinearMap =
      (z : ℂ) • LinearMap.id := by
    ext f
    simp [simpleHomAction, scalarIso, CategoryTheory.Linear.homCongr_apply]
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- A scalar automorphism has FP determinant equal to its unit class weighted
by the actual FP dimension of the object. -/
theorem fpDeterminant_scalar (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (z : ℂˣ) :
    fpDeterminant C X (scalarIso C X z) = fpDimension C X • vafaUnitClass z := by
  unfold fpDeterminant fpDimension
  simp_rw [simpleHomAction_det_scalar, vafaUnitClass_pow]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_comm]

end PropertyF.Ground.CentreModular
