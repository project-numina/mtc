module
public import MTC.PropertyF.Pivotal.SlopeSquare
public import MTC.CategoryTheory.Dimensions.DoubleDualPairing
public import MTC.CategoryTheory.Dimensions.DualBraiding
public import MTC.Center.Dimensions.PivotalTwist
public import MTC.Center.Induction.PivotalFusion

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! Duality of the braided loop underlying the Drinfeld quantum trace. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.PropertyF.Pivotal
universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

local instance : HasRightDual (𝟙_ D) := RightRigidCategory.rightDual _

/-- The braided dimension loop. -/
def braidedLoop (X : D) : (𝟙_ D) ⟶ (𝟙_ D) :=
  η_ X (Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)

set_option backward.isDefEq.respectTransparency false in
/-- Dualizing the braided loop gives the loop of the dual object. -/
theorem braidedLoop_dual (X : D) :
    (rightDualUnitIso (C := D)).inv ≫ (rightAdjointMate (braidedLoop X)) ≫
      (rightDualUnitIso (C := D)).hom = braidedLoop (Xᘁ : D) := by
  simp only [braidedLoop, comp_rightAdjointMate, Category.assoc]
  rw [← rightDualEvaluation_coevaluation X, ← rightDualCoevaluation_evaluation X]
  simp only [Category.assoc]
  rw [← reassoc_of% (rightDualTensorIso_braiding X (Xᘁ))]
  simp only [Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- In a complex fusion category, the braided loop is unchanged by duality. -/
theorem braidedLoop_eq_dual (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    braidedLoop X = braidedLoop (Xᘁ : C.Obj) := by
  let f : End (𝟙_ C.Obj) := End.of (braidedLoop X)
  have hf : braidedLoop X = (unitScalarEquiv C f) • 𝟙 _ := by
    exact congrArg End.asHom (eq_smul_one_of_algEquiv (unitScalarEquiv C) f)
  rw [← braidedLoop_dual X, hf]
  simp only [rightAdjointMate_smul, rightAdjointMate_id, Linear.comp_smul,
    Linear.smul_comp]
  congr 1
  change 𝟙 _ = (rightDualUnitIso (C := C.Obj)).inv ≫ 𝟙 (rightDualObject (𝟙_ C.Obj)) ≫
    (rightDualUnitIso (C := C.Obj)).hom
  simp

set_option backward.isDefEq.respectTransparency false in
/-- On a simple object, the pivotal map is its twist scalar times the Drinfeld map. -/
theorem pivotal_iso_eq_twist_smul (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    (p.iso X).hom = pivotalBraidedTwistScalar C p X • (drinfeldIso X).hom := by
  have h := pivotalBraidedTwist_simple C p X
  change (p.iso X).hom ≫ (drinfeldIso X).inv = _ at h
  apply (cancel_mono (drinfeldIso X).inv).1
  simpa [Linear.smul_comp] using h

set_option backward.isDefEq.respectTransparency false in
/-- The pivotal square differs from the fourth dual by the ratio of the
pivotal twist scalars on a simple object and its dual. -/
theorem pivotalSquare_eq_twist_ratio (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] [Simple (Xᘁ : C.Obj)] :
    (pivotalSquare C p X).hom =
      (pivotalBraidedTwistScalar C p X / pivotalBraidedTwistScalar C p (Xᘁ : C.Obj)) •
        (fourthDualIso X).hom := by
  have hd := pivotal_iso_eq_twist_smul C p (Xᘁ : C.Obj)
  have hn := pivotalBraidedTwistScalar_ne_zero C p (Xᘁ : C.Obj)
  have hi := iso_inv_eq_inv_smul hn hd
  have hp : ((p.iso X).homᘁ)ᘁ =
      (pivotalBraidedTwistScalar C p (Xᘁ : C.Obj))⁻¹ •
        ((drinfeldIso (Xᘁ : C.Obj)).invᘁ) := by
    have hdual := congrArg Iso.inv (pivotal_dual p X)
    change (p.iso (Xᘁ)).inv = ((p.iso X).homᘁ) at hdual
    rw [← hdual, hi, rightAdjointMate_smul]
  simp only [pivotalSquare, Iso.trans_hom, rightDualIsoMap]
  rw [hp, pivotal_iso_eq_twist_smul C p X]
  simp [fourthDualIso, rightDualIsoMap, Linear.comp_smul, Linear.smul_comp,
    smul_smul, div_eq_mul_inv, mul_comm]

/-- The quantum trace of the Drinfeld map is the braided dimension loop. -/
theorem rightQuantumTrace_drinfeld (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    rightQuantumTrace (drinfeldIso X) = End.of (braidedLoop X) := by
  apply End.ext
  simp only [rightQuantumTrace, braidedLoop, tensorHom_def, whiskerLeft_id,
    Category.comp_id, drinfeld_eval]

/-- The pivotal dimension is the twist scalar times the braided loop scalar. -/
theorem pivotalDimension_eq_twist_mul_loop (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    pivotalDimension C p X = pivotalBraidedTwistScalar C p X *
      unitScalar C (End.of (braidedLoop X)) := by
  rw [pivotalDimension, rightTrace_id,
    rightQuantumTrace_smul_hom (pivotal_iso_eq_twist_smul C p X), rightQuantumTrace_drinfeld C]
  simp [unitScalar_eq_equiv, smul_eq_mul]

/-- The pivotal dimension of a simple dual is the conjugate dimension. -/
theorem pivotalDimension_dual_conj (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    pivotalDimension C p (Xᘁ : C.Obj) = star (pivotalDimension C p X) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C X
  rw [pivotalDimension_iso p (rightDualIsoMap e.symm),
    MTC.Center.Induction.pivotalDimension_simple_dual_conj,
    pivotalDimension_iso p e]

/-- The actual pivotal/fourth-dual comparison scalar is the ratio of the
pivotal dimension of a simple object to its conjugate. -/
theorem pivotalFourthScalar_eq_dimension_ratio (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    pivotalFourthScalar C p X =
      pivotalDimension C p X / star (pivotalDimension C p X) := by
  let : Simple (Xᘁ : C.Obj) := simple_rightDual X
  let a := pivotalBraidedTwistScalar C p X
  let b := pivotalBraidedTwistScalar C p (Xᘁ : C.Obj)
  let l := unitScalar C (End.of (braidedLoop X))
  have hq : pivotalFourthScalar C p X = a / b := by
    apply smul_left_injective ℂ (id_nonzero X)
    change pivotalFourthScalar C p X • 𝟙 X = (a / b) • 𝟙 X
    rw [← pivotalFourthComparison_simple]
    simp only [pivotalFourthComparison, Iso.trans_hom, Iso.symm_hom,
      pivotalSquare_eq_twist_ratio, Linear.smul_comp, Iso.hom_inv_id, a, b]
  have hd : pivotalDimension C p X = a * l :=
    pivotalDimension_eq_twist_mul_loop C p X
  have hddual : star (pivotalDimension C p X) = b * l := by
    rw [← pivotalDimension_dual_conj C p X,
      pivotalDimension_eq_twist_mul_loop C p (Xᘁ : C.Obj), ← braidedLoop_eq_dual C X]
  have hn : pivotalDimension C p X ≠ 0 := by
    simpa only [pivotalDimension] using MTC.Modular.unitScalar_rightTrace_ne_zero C p X
  have hl : l ≠ 0 := by
    intro hz
    apply hn
    rw [hd, hz, mul_zero]
  rw [hq, hddual, hd]
  exact (mul_div_mul_right a b hl).symm

/-- The quotient by the conjugate equals the square of the unit phase. -/
theorem complex_div_star_eq_phase_sq (z : ℂ) (hz : z ≠ 0) :
    z / star z = (z / (‖z‖ : ℂ)) ^ 2 := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hs : star z ≠ 0 := by simpa using ((map_ne_zero (starRingEnd ℂ)).2 hz)
  have h : (‖z‖ : ℂ) ^ 2 = z * star z := by
    simpa only [Complex.ofReal_pow, Complex.star_def] using (Complex.mul_conj' z).symm
  field_simp
  rw [h]

/-- Simple constituents of the tensor square have the phase required by
pivotal trace saturation. -/
theorem pivotalDimension_tensor_square_phase (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X Y : C.Obj) [Simple X] [Simple Y]
    (f : Y ⟶ X ⊗ X) (hf : f ≠ 0) :
    pivotalDimension C p Y =
      (pivotalDimension C p X / (‖pivotalDimension C p X‖ : ℂ)) ^ 4 *
        star (pivotalDimension C p Y) := by
  have hx : pivotalDimension C p X ≠ 0 := by
    simpa only [pivotalDimension] using MTC.Modular.unitScalar_rightTrace_ne_zero C p X
  have hy : pivotalDimension C p Y ≠ 0 := by
    simpa only [pivotalDimension] using MTC.Modular.unitScalar_rightTrace_ne_zero C p Y
  have hc := pivotalFourthScalar_tensor_of_hom C p X X Y f hf
  simp only [pivotalFourthScalar_eq_dimension_ratio] at hc
  rw [complex_div_star_eq_phase_sq _ hx] at hc
  have hstar : star (pivotalDimension C p Y) ≠ 0 := by
    simpa using ((map_ne_zero (starRingEnd ℂ)).2 hy)
  apply (div_eq_iff hstar).mp
  simpa [pow_two, pow_succ, mul_assoc] using hc

end MTC.PropertyF.Pivotal
end
