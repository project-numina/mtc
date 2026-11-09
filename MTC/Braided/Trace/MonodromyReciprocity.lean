module
public import MTC.Algebra.ComplexBlockTrace
public import MTC.Braided.Trace.InverseMonodromy
public import MTC.Braided.Trace.MonodromyBound

/-! Phase reciprocity for actual monodromy traces. -/

open MTC.Algebra MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators ComplexConjugate

@[expose] public noncomputable section
namespace MTC.Braided.Trace
universe v u

/-- The inverse two-strand braid-square trace is inverse monodromy trace. -/
theorem actual_two_inverse_braid_trace (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    actualBraidTrace C p (braidInImage ((imageGenerator X 0 0 ^ 2)⁻¹)) =
      scalarTrace p (MTC.Fusion.unitScalarEquiv C) (inverseSelfMonodromy X) := by
  simp only [actualBraidTrace, imageGenerator, braidInImage_val, braidEndRepresentation,
    MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, scalarTrace]
  simp only [Subgroup.coe_inv, Subgroup.coe_pow]
  rw [← rightTrace_iso_conj (twoPowerIso X) p]
  congr 2
  have hgen : (twoPowerIso X).conj (Aut.toEnd (braidGenerator X 0 0)⁻¹) =
      End.of (β_ X X).inv := by
    apply End.ext
    change ((twoPowerIso X).conjAut (braidGenerator X 0 0)⁻¹).asIso.hom = _
    rw [map_inv]
    exact congrArg Iso.inv (twoGenerator_transport X)
  rw [← inv_pow, map_pow, map_pow, hgen]
  simp [inverseSelfMonodromy, pow_two, End.mul_asHom]

/-- A common unit-modulus phase for every simple constituent of the actual
square tensor power implies equality of the forward and inverse monodromy trace
norms. The multiplicities, braid blocks, and unitarity are all constructed
from the actual category and its finite braid image. -/
theorem norm_inverse_monodromy_trace_eq_of_constituent_phase
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    {X : C.Obj} [Simple X] (hfinite : ObjectPropertyF X) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (hphase : ∀ i : Fin (MTC.Fusion.rank C),
      0 < Module.finrank ℂ (MTC.Fusion.simples C i ⟶ braidTensorPower X 0) →
      pivotalDimension C p (MTC.Fusion.simples C i) =
        ξ * star (pivotalDimension C p (MTC.Fusion.simples C i))) :
    ‖scalarTrace p (MTC.Fusion.unitScalarEquiv C) (inverseSelfMonodromy X)‖ =
      ‖scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X)‖ := by
  classical
  obtain ⟨r, size, b, mult, hsize, he, _, hdim, htrace⟩ :=
    exists_unitary_braid_trace_blocks C p (MTC.Fusion.unitScalarEquiv C) (hfinite 0)
  let B : Blocks := ⟨r, size⟩
  let w : Fin r → ℂ := fun j => ∑ i, (mult i j : ℂ) *
    pivotalDimension C p (MTC.Fusion.simples C i)
  have htr : ∀ z : braidAlgebra X 0, actualBraidTrace C p z = B.complexTrace w (b z) := by
    intro z
    simpa [actualBraidTrace, Blocks.complexTrace, pivotalDimension, unitScalar_eq_equiv, B, w]
      using htrace z
  have hw : ∀ j, w j = ξ * star (w j) := by
    intro j
    change (∑ i, (mult i j : ℂ) * pivotalDimension C p (MTC.Fusion.simples C i)) =
      ξ * (starRingEnd ℂ) (∑ i, (mult i j : ℂ) *
        pivotalDimension C p (MTC.Fusion.simples C i))
    simp only [map_sum, map_mul, map_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hm : mult i j = 0
    · simp [hm]
    · have hle : mult i j * size j ≤
          Module.finrank ℂ (MTC.Fusion.simples C i ⟶ braidTensorPower X 0) := by
        simpa only [← hdim i] using
          (Finset.single_le_sum (f := fun j => mult i j * size j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      have hp := hphase i (lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero hm) (hsize j)) hle)
      conv_lhs => rw [hp]
      exact mul_left_comm _ _ _

  let g : braidImage X 0 := imageGenerator X 0 0 ^ 2
  let ρ : braidImage X 0 →* B.Matrices :=
    b.toMonoidHom.comp (braidInImage (X := X) (n := 0))
  have hn := B.norm_complexTrace_star_of_weight_phase w ξ hξ hw (ρ g)
  have hstar : star (ρ g) = ρ g⁻¹ := by
    simpa only [← map_inv, MonoidHom.coe_toHomUnits] using
      unitary_star_coe_inv (ρ.toHomUnits g) (he g)
  rw [hstar] at hn
  change ‖B.complexTrace w (b (braidInImage g⁻¹))‖ =
    ‖B.complexTrace w (b (braidInImage g))‖ at hn
  rw [← htr, ← htr] at hn
  change ‖actualBraidTrace C p (braidInImage ((imageGenerator X 0 0 ^ 2)⁻¹))‖ =
    ‖actualBraidTrace C p (braidInImage (imageGenerator X 0 0 ^ 2))‖ at hn
  rw [actual_two_inverse_braid_trace, actual_two_braid_trace] at hn
  exact hn

/-- Saturation under the explicit tensor-square phase premise. Establishing that
premise for arbitrary pivotal fusion categories is a separate slope theorem. -/
theorem saturation_of_constituent_phase
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    {X : C.Obj} [Simple X] (hfinite : ObjectPropertyF X) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (hphase : ∀ i : Fin (MTC.Fusion.rank C),
      0 < Module.finrank ℂ (MTC.Fusion.simples C i ⟶ braidTensorPower X 0) →
      pivotalDimension C p (MTC.Fusion.simples C i) =
        ξ * star (pivotalDimension C p (MTC.Fusion.simples C i)))
    (hmax : ‖scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) /
      pivotalDimension C p X‖ = MTC.Fusion.fpDimension C X) :
    ‖pivotalDimension C p X‖ = MTC.Fusion.fpDimension C X :=
  dimension_norm_eq_fp_of_inverse_trace_norm C p hfinite hmax
    (norm_inverse_monodromy_trace_eq_of_constituent_phase C p hfinite ξ hξ hphase)

end MTC.Braided.Trace
