module
public import MTC.Braided.Trace.ComplexSaturation

/-! Inverse self-monodromy and the mixed-sign three-strand overlap. -/

open MTC.Algebra MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory

@[expose] public noncomputable section
namespace MTC.Braided.Trace
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The inverse double self-braiding on the ordinary two-fold tensor product. -/
def inverseSelfMonodromy (X : C) : End (X ⊗ X) :=
  End.of ((β_ X X).inv ≫ (β_ X X).inv)

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse right generator after removing the trailing tensor unit. -/
theorem threeGeneratorRight_inv_transport (X : C) :
    (threePowerIso X).conj (Aut.toEnd ((braidGenerator X 1 1)⁻¹)) =
      End.of (X ◁ (β_ X X).inv) := by
  apply End.ext
  change ((threePowerIso X).conjAut ((braidGenerator X 1 1)⁻¹)).asIso.hom = _
  rw [map_inv]
  exact congrArg Iso.inv (show ((threePowerIso X).conjAut (braidGenerator X 1 1)).asIso =
    whiskerLeftIso X (β_ X X) from Iso.ext (threeGeneratorRight_transport X))

omit [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Mixed-sign double braids are the overlap of monodromy and its inverse. -/
theorem three_braid_mixed_overlap (X : C) :
    (threePowerIso X).conj
      (Aut.toEnd ((braidGenerator X 1 0) ^ 2 * ((braidGenerator X 1 1) ^ 2)⁻¹)) =
    (α_ X X X).conj (overlapEndProduct (selfMonodromy X) (inverseSelfMonodromy X)) := by
  rw [map_mul, map_mul, map_pow, map_pow, ← inv_pow, map_pow, map_pow,
    threeGeneratorLeft_end_transport, threeGeneratorRight_inv_transport]
  apply End.ext
  simp [overlapEndProduct, insertRightIdentity, overlapFresh, selfMonodromy,
    inverseSelfMonodromy, Iso.conj_apply_asHom, pow_two, End.mul_asHom, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc]

/-- The actual mixed-sign three-strand trace is the product of the two
monodromy traces divided by the simple strand dimension. -/
theorem actual_mixed_three_braid_trace (D : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (X : D.Obj) [Simple X] :
    actualBraidTrace D p (braidInImage
      (threeGeneratorLeft X ^ 2 * (threeGeneratorRight X ^ 2)⁻¹)) =
      scalarTrace p (MTC.Fusion.unitScalarEquiv D) (selfMonodromy X) *
      scalarTrace p (MTC.Fusion.unitScalarEquiv D) (inverseSelfMonodromy X) /
        pivotalDimension D p X := by
  simp only [actualBraidTrace, threeGeneratorLeft, threeGeneratorRight, imageGenerator,
    braidInImage_val, braidEndRepresentation,
    MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, pivotalDimension,
    unitScalar_eq_equiv, scalarTrace]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
  rw [← rightTrace_iso_conj (threePowerIso X) p, three_braid_mixed_overlap,
    rightTrace_iso_conj, pivotalTrace_overlap, mul_div_assoc]

/-- The actual identity braid on three strands has trace `d_X³`. -/
theorem actual_three_identity_trace (D : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (X : D.Obj) :
    actualBraidTrace D p (1 : braidAlgebra X 1) = pivotalDimension D p X ^ 3 := by
  have h := pivotalDimension_iso p (threePowerIso X)
  rw [pivotalDimension_tensor, pivotalDimension_tensor] at h
  simpa [actualBraidTrace, pivotalDimension, unitScalar_eq_equiv, braidTensorPower, pow_succ, mul_assoc] using h

/-- The remaining scalar step of saturation, provided the trace of inverse
monodromy has the same norm as that of monodromy. This norm equality is a
separate pivotal phase/reciprocity obligation. -/
theorem dimension_norm_eq_fp_of_inverse_trace_norm
    (D : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := D.Obj))
    {X : D.Obj} [Simple X] (hfinite : ObjectPropertyF X)
    (hmax : ‖scalarTrace p (MTC.Fusion.unitScalarEquiv D) (selfMonodromy X) /
      pivotalDimension D p X‖ = MTC.Fusion.fpDimension D X)
    (hinv : ‖scalarTrace p (MTC.Fusion.unitScalarEquiv D) (inverseSelfMonodromy X)‖ =
      ‖scalarTrace p (MTC.Fusion.unitScalarEquiv D) (selfMonodromy X)‖) :
    ‖pivotalDimension D p X‖ = MTC.Fusion.fpDimension D X := by
  have hf : 0 ≤ MTC.Fusion.fpDimension D X :=
    le_of_lt (lt_of_lt_of_le zero_lt_one (MTC.Fusion.one_le_fpDimension (Simple.not_isZero X)))
  apply norm_eq_of_mixed_trace_saturation (Modular.unitScalar_rightTrace_ne_zero D p X)
    hf hmax hinv
  have h := actual_mixed_braid_trace_of_maximal_monodromy D p hfinite hmax
  rw [actual_mixed_three_braid_trace, actual_three_identity_trace] at h
  exact h

end MTC.Braided.Trace
