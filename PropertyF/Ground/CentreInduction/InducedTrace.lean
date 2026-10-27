module
public import PropertyF.Ground.CentreInduction.InjectiveFusion
public import PropertyF.Ground.Dimensions.PivotalUniqueness
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

/-- Agreement with FP dimension on simples extends to all objects. -/
theorem pivotalDimension_eq_fp (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (X : C.Obj) : Dimensions.pivotalDimension C p X = (fpDimension C X : ℂ) := by
  rw [Dimensions.pivotalDimension_decomposition]
  unfold fpDimension
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, hsimple]

/-- The induction of the tensor unit has base pivotal dimension FPdim(C). -/
theorem induced_unit_dimension (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ)) :
    Dimensions.pivotalDimension C p (underlying C (𝟙_ C.Obj)) = (globalFPDimension C : ℂ) := by
  rw [pivotalDimension_eq_fp C p hsimple, fpDimension_underlying, fpDimension_unit, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- A centre pivotal structure with the displayed single trace compatibility
constructs centre fusion when the base pivotal dimensions equal FP dimensions. -/
theorem center_fusion_of_compatible_pivotal (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : (pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj)))).asHom.f =
      (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))).asHom) :
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  apply center_fusion_of_nonzero_induced_trace C (𝟙_ C.Obj) pZ
  intro hz
  have hbase : (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))) = 0 := by
    apply End.ext
    rw [← hcompat, hz]
    rfl
  have hd := induced_unit_dimension C p hsimple
  change unitScalar C (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))) = _ at hd
  rw [hbase] at hd
  have hpos : 0 < globalFPDimension C := lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  have hne : (globalFPDimension C : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hzero : unitScalar C 0 = 0 := by
    rw [← Dimensions.groundUnitScalarEquiv_apply]
    exact map_zero _
  rw [hzero] at hd
  exact hne hd.symm

/-- A positive base pivotal structure supplies the nonzero induced dimension;
only the displayed centre trace compatibility remains to be constructed. -/
theorem center_fusion_of_positive_compatible_pivotal
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i)
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : (pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj)))).asHom.f =
      (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))).asHom) :
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  apply center_fusion_of_compatible_pivotal C p ?_ pZ hcompat
  intro i
  rw [hreal, Dimensions.positive_pivotalDimension_eq_fpSimple C p d hreal hpos]

end PropertyF.Ground.CentreInduction
