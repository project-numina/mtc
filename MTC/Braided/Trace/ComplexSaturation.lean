module
public import MTC.Algebra.ComplexBraidSaturation
public import MTC.Braided.Trace.ComplexTraceBound

/-!
# Saturation on actual categorical braid blocks

The equality argument is applied to the finite-image braid algebra with its
actual complex multiplicity weights, including weights which may vanish.
-/

open MTC.Algebra MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators

@[expose] public noncomputable section
namespace MTC.Braided.Trace
universe v u

/-- A saturated unitary block presentation turns the mixed three-strand
braid trace into the identity trace. Zero weights are allowed. -/
theorem actual_mixed_braid_trace_eq_one_of_block_saturation
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    {X : C.Obj} (B : Blocks) (b : BraidBlockPresentation X 1 B.size)
    (w : Fin B.count → ℂ) (he : IsUnitaryBraidPresentation b)
    (htr : ∀ z : braidAlgebra X 1, actualBraidTrace C p z = B.complexTrace w (b z))
    (hsat : ‖B.complexTrace w
      (b (braidInImage (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)))‖ =
      B.complexMass w) :
    actualBraidTrace C p (braidInImage
      (threeGeneratorLeft X ^ 2 * (threeGeneratorRight X ^ 2)⁻¹)) =
      actualBraidTrace C p (1 : braidAlgebra X 1) := by
  let ρ : braidImage X 1 →* B.Matrices :=
    b.toMonoidHom.comp (braidInImage (X := X) (n := 1))
  let a : B.Matricesˣ := ρ.toHomUnits (threeGeneratorLeft X)
  let c : B.Matricesˣ := ρ.toHomUnits (threeGeneratorRight X)
  have ha : B.IsUnitary (a : B.Matrices) := he _
  have hc : B.IsUnitary (c : B.Matrices) := he _
  have hbraid : a * c * a = c * a * c := Units.ext (by
    simpa only [a, c, Units.val_mul, MonoidHom.coe_toHomUnits, map_mul] using
      congrArg ρ (three_braid_image_relation X))
  have hpos : ((a ^ 2 * c ^ 2 : B.Matricesˣ) : B.Matrices) =
      b (braidInImage (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) := by
    simp only [a, c, ← map_pow, ← map_mul, MonoidHom.coe_toHomUnits]
    rfl
  have hmixed := B.mixed_braid_trace_eq_one_of_saturation w ha hc hbraid (hpos ▸ hsat)
  have hmix : ((a ^ 2 * (c ^ 2)⁻¹ : B.Matricesˣ) : B.Matrices) =
      b (braidInImage (threeGeneratorLeft X ^ 2 * (threeGeneratorRight X ^ 2)⁻¹)) := by
    simp only [a, c, ← map_pow, ← map_inv, ← map_mul, MonoidHom.coe_toHomUnits]
    rfl
  rw [hmix, ← htr, ← map_one b, ← htr] at hmixed
  exact hmixed

/-- If the actual three-strand overlap attains the sharp unitary trace bound,
then the mixed-sign three-strand braid has the trace of the identity. -/
theorem actual_mixed_braid_trace_eq_one_of_saturation
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    {X : C.Obj} [Simple X] (hfinite : ObjectPropertyF X)
    (hvalue : ‖actualBraidTrace C p (braidInImage
      (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2))‖ =
      ‖pivotalDimension C p X‖ * MTC.Fusion.fpDimension C X ^ 2) :
    actualBraidTrace C p (braidInImage
      (threeGeneratorLeft X ^ 2 * (threeGeneratorRight X ^ 2)⁻¹)) =
      actualBraidTrace C p (1 : braidAlgebra X 1) := by
  classical
  obtain ⟨r, size, b, mult, _, he, _, _, htrace⟩ :=
    exists_unitary_braid_trace_blocks C p (MTC.Fusion.unitScalarEquiv C) (hfinite 1)
  let B : Blocks := ⟨r, size⟩
  let w : Fin r → ℂ := fun j => ∑ i, (mult i j : ℂ) *
    MTC.Fusion.unitScalarEquiv C (p.rightTrace (𝟙 (MTC.Fusion.simples C i)))
  have htr : ∀ z : braidAlgebra X 1, actualBraidTrace C p z = B.complexTrace w (b z) := by
    intro z
    simpa [actualBraidTrace, Blocks.complexTrace, B, w] using htrace z
  apply actual_mixed_braid_trace_eq_one_of_block_saturation C p B b w he htr
  apply B.complexTrace_saturates_of_maximal_bound w (he _)
    (R := ‖pivotalDimension C p X‖ * MTC.Fusion.fpDimension C X ^ 2)
  · intro u hu
    simpa [htr] using pivotal_unitary_trace_bound C p hfinite b he (b.symm u) (by simpa using hu)
  · change ‖B.complexTrace w
      (b (braidInImage (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)))‖ = _
    rw [← htr]
    exact hvalue

/-- A maximal normalized self-monodromy trace gives the mixed-braid identity
for actual categorical traces. -/
theorem actual_mixed_braid_trace_of_maximal_monodromy
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    {X : C.Obj} [Simple X] (hfinite : ObjectPropertyF X)
    (hmax : ‖scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) /
      pivotalDimension C p X‖ = MTC.Fusion.fpDimension C X) :
    actualBraidTrace C p (braidInImage
      (threeGeneratorLeft X ^ 2 * (threeGeneratorRight X ^ 2)⁻¹)) =
      actualBraidTrace C p (1 : braidAlgebra X 1) := by
  apply actual_mixed_braid_trace_eq_one_of_saturation C p hfinite
  have hd : pivotalDimension C p X ≠ 0 := Modular.unitScalar_rightTrace_ne_zero C p X
  rw [norm_div, div_eq_iff (norm_ne_zero_iff.mpr hd)] at hmax
  rw [actual_three_braid_trace, norm_div, norm_pow, hmax]
  rw [div_eq_iff (norm_ne_zero_iff.mpr hd)]
  ring

end MTC.Braided.Trace
