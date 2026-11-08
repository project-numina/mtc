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
  let ρ : braidImage X 1 →* B.Matrices :=
    b.toMonoidHom.comp (braidInImage (X := X) (n := 1))
  let a : B.Matricesˣ := ρ.toHomUnits (threeGeneratorLeft X)
  let c : B.Matricesˣ := ρ.toHomUnits (threeGeneratorRight X)
  have ha : B.IsUnitary (a : B.Matrices) := he _
  have hc : B.IsUnitary (c : B.Matrices) := he _
  have hbraid : a * c * a = c * a * c := Units.ext (by
    simpa only [a, c, Units.val_mul, MonoidHom.coe_toHomUnits, map_mul] using
      congrArg ρ (three_braid_image_relation X))
  have hunit : B.IsUnitary ((a ^ 2 * c ^ 2 : B.Matricesˣ) : B.Matrices) := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
      (unitary B.Matrices).mul_mem ((unitary B.Matrices).pow_mem ha 2)
        ((unitary B.Matrices).pow_mem hc 2)
  have hpos : ((a ^ 2 * c ^ 2 : B.Matricesˣ) : B.Matrices) =
      b (braidInImage (threeGeneratorLeft X ^ 2 * threeGeneratorRight X ^ 2)) := by
    change ((ρ.toHomUnits (threeGeneratorLeft X) ^ 2 *
      ρ.toHomUnits (threeGeneratorRight X) ^ 2 : B.Matricesˣ) : B.Matrices) = _
    rw [← map_pow, ← map_pow, ← map_mul]
    rfl
  have hmix : ((a ^ 2 * (c ^ 2)⁻¹ : B.Matricesˣ) : B.Matrices) =
      b (braidInImage (threeGeneratorLeft X ^ 2 * (threeGeneratorRight X ^ 2)⁻¹)) := by
    change ((ρ.toHomUnits (threeGeneratorLeft X) ^ 2 *
      (ρ.toHomUnits (threeGeneratorRight X) ^ 2)⁻¹ : B.Matricesˣ) : B.Matrices) = _
    rw [← map_pow, ← map_pow, ← map_inv, ← map_mul]
    rfl
  have hnorm : ‖B.complexTrace w ((a ^ 2 * c ^ 2 : B.Matricesˣ) : B.Matrices)‖ =
      ‖pivotalDimension C p X‖ * MTC.Fusion.fpDimension C X ^ 2 := by
    rw [hpos, ← htr]
    exact hvalue
  have hmass : B.complexMass w ≤ ‖pivotalDimension C p X‖ *
      MTC.Fusion.fpDimension C X ^ 2 :=
    B.complexMass_le_of_unitary_trace_bound w (fun u hu => by
      simpa [htr] using pivotal_unitary_trace_bound C p hfinite b he (b.symm u) (by simpa using hu))
  have hsat : ‖B.complexTrace w ((a ^ 2 * c ^ 2 : B.Matricesˣ) : B.Matrices)‖ =
      B.complexMass w := le_antisymm (B.norm_complexTrace_le w hunit) (hnorm ▸ hmass)
  have hmixed := B.mixed_braid_trace_eq_one_of_saturation w a c ha hc hbraid hsat
  rw [hmix, ← htr, ← map_one b, ← htr] at hmixed
  exact hmixed

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
  have hd : pivotalDimension C p X ≠ 0 := by
    simpa only [pivotalDimension] using Modular.unitScalar_rightTrace_ne_zero C p X
  rw [actual_three_braid_trace]
  have heq : scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) ^ 2 /
      pivotalDimension C p X = pivotalDimension C p X *
        (scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) /
          pivotalDimension C p X) ^ 2 := by
    field_simp
  rw [heq, norm_mul, norm_pow, hmax]

end MTC.Braided.Trace
