module
public import MTC.Braided.Trace.ComplexTraceBound

/-! The two-strand consequence of the general pivotal trace bound. -/

open MTC.Algebra MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory

@[expose] public noncomputable section
namespace MTC.Braided.Trace
universe v u

/-- After removing the trailing tensor unit, the two-strand generator is
exactly the braiding on the ordinary tensor square. -/
theorem twoGenerator_transport {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] (X : D) :
    ((twoPowerIso X).conjAut (braidGenerator X 0 0)).asIso = β_ X X := by
  apply Iso.ext
  change (twoPowerIso X).inv ≫ (braidGenerator X 0 0).asIso.hom ≫
    (twoPowerIso X).hom = _
  simp [twoPowerIso, braidGenerator, tensorPower]

/-- Two-strand braid-square trace is the categorical self-monodromy trace. -/
theorem actual_two_braid_trace (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    actualBraidTrace C p (braidInImage (imageGenerator X 0 0 ^ 2)) =
      scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) := by
  simp only [actualBraidTrace, imageGenerator, braidInImage_val,
    braidEndRepresentation, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
    scalarTrace]
  rw [← rightTrace_iso_conj (twoPowerIso X) p]
  congr 2
  change ((twoPowerIso X).conj (Aut.toEnd ((braidGenerator X 0 0) ^ 2))).asHom = _
  have hgen : (twoPowerIso X).conj (Aut.toEnd (braidGenerator X 0 0)) =
      End.of (β_ X X).hom := End.ext (congrArg Iso.hom (twoGenerator_transport X))
  rw [map_pow, map_pow, hgen]
  simp [selfMonodromy, pow_two, End.mul_asHom]

/-- The normalized self-monodromy trace has norm at most the FP dimension. -/
theorem norm_monodromy_trace_div_dimension_le_fp
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    {X : C.Obj} [Simple X] (hfinite : ObjectPropertyF X) :
    ‖scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) /
      pivotalDimension C p X‖ ≤ MTC.Fusion.fpDimension C X := by
  classical
  let : Finite (braidImage X 0) := hfinite 0
  obtain ⟨r, size, b, _, hb⟩ := groupImageAlgebra_unitary_blocks (braidEndRepresentation X 0)
  have hbound := pivotal_unitary_trace_bound C p hfinite b hb
    (braidInImage (imageGenerator X 0 0 ^ 2)) (hb (imageGenerator X 0 0 ^ 2))
  rw [actual_two_braid_trace] at hbound
  simp only [Nat.zero_add, pow_one] at hbound
  have hd : 0 < ‖pivotalDimension C p X‖ := norm_pos_iff.mpr (by
    simpa only [pivotalDimension] using Modular.unitScalar_rightTrace_ne_zero C p X)
  rw [norm_div, div_le_iff₀ hd]
  simpa [mul_comm] using hbound

end MTC.Braided.Trace
