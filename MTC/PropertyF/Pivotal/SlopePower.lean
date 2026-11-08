module
public import MTC.PropertyF.Pivotal.SlopeTrace
public import MTC.Braided.Definitions

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! Pivotal dimension phases of simple tensor-power constituents. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
local instance : HasRightDual (𝟙_ C.Obj) := RightRigidCategory.rightDual _

set_option backward.isDefEq.respectTransparency false in
/-- The pivotal/fourth-dual comparison is the identity on the tensor unit. -/
theorem pivotalFourthComparison_unit :
    (pivotalFourthComparison C p (𝟙_ C.Obj)).hom = 𝟙 _ := by
  have h : pivotalSquare C p (𝟙_ C.Obj) = fourthDualIso (𝟙_ C.Obj) := by
    apply Iso.ext
    simp only [pivotalSquare, Iso.trans_hom, rightDualIsoMap,
      fourthDualIso_unit, p.unit]
  simp [pivotalFourthComparison, h]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison acts on an actual tensor power as the corresponding
power of its simple scalar. -/
theorem pivotalFourthComparison_tensorPower (X : C.Obj) [Simple X] (n : ℕ) :
    (pivotalFourthComparison C p (tensorPower X n)).hom =
      (pivotalFourthScalar C p X) ^ n • 𝟙 _ := by
  induction n with
  | zero => simp [tensorPower, pivotalFourthComparison_unit]
  | succ n ih =>
    rw [tensorPower, pivotalFourthComparison_tensor, pivotalFourthComparison_simple, ih]
    simp [tensorHom_def, MonoidalLinear.whiskerLeft_smul,
      MonoidalLinear.smul_whiskerRight, Linear.comp_smul,
      smul_smul, pow_succ, mul_comm]

/-- The comparison scalar of a simple object occurring in an actual tensor
power is the corresponding power of the original simple's scalar. -/
theorem pivotalFourthScalar_tensorPower_of_hom (X Y : C.Obj) [Simple X] [Simple Y]
    (n : ℕ) (f : Y ⟶ tensorPower X n) (hf : f ≠ 0) :
    pivotalFourthScalar C p Y = (pivotalFourthScalar C p X) ^ n := by
  have h := pivotalFourthComparison_natural C p f
  rw [pivotalFourthComparison_tensorPower, pivotalFourthComparison_simple] at h
  simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp] at h
  exact (smul_left_injective ℂ hf h).symm

/-- Every simple constituent of a tensor power has the pivotal phase predicted
by the power. -/
theorem pivotalDimension_tensorPower_phase (X Y : C.Obj) [Simple X] [Simple Y]
    (n : ℕ) (f : Y ⟶ tensorPower X n) (hf : f ≠ 0) :
    pivotalDimension C p Y =
      (pivotalDimension C p X / (‖pivotalDimension C p X‖ : ℂ)) ^ (2 * n) *
        star (pivotalDimension C p Y) := by
  have hx : pivotalDimension C p X ≠ 0 := by
    simpa only [pivotalDimension] using MTC.Modular.unitScalar_rightTrace_ne_zero C p X
  have hy : pivotalDimension C p Y ≠ 0 := by
    simpa only [pivotalDimension] using MTC.Modular.unitScalar_rightTrace_ne_zero C p Y
  have hc := pivotalFourthScalar_tensorPower_of_hom C p X Y n f hf
  simp only [pivotalFourthScalar_eq_dimension_ratio] at hc
  rw [complex_div_star_eq_phase_sq _ hx, ← pow_mul] at hc
  have hstar : star (pivotalDimension C p Y) ≠ 0 := by
    simpa using ((map_ne_zero (starRingEnd ℂ)).2 hy)
  exact (div_eq_iff hstar).mp hc

end MTC.PropertyF.Pivotal
end
