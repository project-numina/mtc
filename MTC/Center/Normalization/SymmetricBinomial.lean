module
public import MTC.Center.Normalization.AlgebraicDimension
public import MTC.Center.Normalization.SymmetricPivotal
public import MTC.Center.Trace.LeftTensorTrace

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.Center.Trace

/-! # Algebraic integrality of symmetric falling binomials

Alternating permutation projectors prove that each generalized falling
binomial of a simple object's canonical symmetric pivotal dimension is an
algebraic integer. The further arithmetic implication that the dimension is
an ordinary integer is not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped BigOperators
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _)

/-- The canonical symmetric pivotal twist acts by one on every simple. -/
theorem canonicalSymmetricPivotal_twist_one (X : C.Obj) [Simple X] :
    pivotalBraidedTwistScalar C (canonicalSymmetricPivotal hsym) X = 1 := by
  have htwist : (pivotalBraidedTwist C (canonicalSymmetricPivotal hsym) X).hom = 𝟙 X := by
    change (drinfeldIso X).hom ≫ (MTC.Fusion.doubleDualIso C X).inv = 𝟙 X
    have h : MTC.Fusion.doubleDualIso C X = drinfeldIso X := rfl
    rw [h, Iso.hom_inv_id]
  apply smul_left_injective ℂ (id_nonzero X)
  simpa only [one_smul, htwist] using (pivotalBraidedTwist_simple C (canonicalSymmetricPivotal hsym) X).symm

/-- The actual permutation traces satisfy fixed- and moved-strand deletion
for the canonical symmetric pivotal structure. -/
theorem canonicalSymmetricPivotal_traceDeletion (X : C.Obj) [Simple X] :
    let p := canonicalSymmetricPivotal hsym
    let hX : SelfTransparent X := hsym X X
    IsTraceDeletion (permScalarTrace C p (tensorPermAction X hX)) (pivotalDimension C p X) := by
  let p := canonicalSymmetricPivotal hsym
  let hX : SelfTransparent X := hsym X X
  have hp : p.IsSpherical := canonicalSymmetricPivotal_spherical C hsym
  have ht : IsLeftTraceCompatible p X := fun _ f ↦ spherical_rightTrace_leftPartialTrace p hp f
  have hfirst (n : ℕ) : leftPartialTrace p (Aut.toEnd (braidGenerator X n 0)) = (1 : ℂ) • 1 := by
    have ht' := leftPartialTrace_firstGenerator_of_trace_compatibility (C := C) (p := p) n
        (ht X (End.of (β_ X X).hom))
    rw [show pivotalBraidedTwistScalar C p X = 1 from canonicalSymmetricPivotal_twist_one C hsym X] at ht'
    exact ht'
  have hadj : HasAdjacentTrace (permScalarTrace C p (tensorPermAction X hX)) := fun n σ ↦ by
    simpa [permScalarTrace, scalarPermTrace] using
      tensorPermTrace_adjacent p (unitScalarEquiv C).toLinearMap hX ht 1 hfirst σ
  refine ⟨?_, movedTrace_of_adjacent (unitScalarEquiv C) (tensorPermAction X hX) hadj⟩
  intro n σ
  simpa [permScalarTrace, scalarPermTrace, fixHead, pivotalDimension, unitScalar_eq_equiv] using
    tensorPermTrace_fixHead p (unitScalarEquiv C) hX σ

/-- Every generalized falling binomial of a simple object's canonical
symmetric pivotal dimension is an algebraic integer. -/
theorem canonicalSymmetricPivotal_falling_binomial_isIntegral
    (X : C.Obj) [Simple X] (n : ℕ) :
    IsIntegral ℤ ((∏ k ∈ Finset.range n,
      (pivotalDimension C (canonicalSymmetricPivotal hsym) X - (k : ℂ))) / (n.factorial : ℂ)) := by
  let p := canonicalSymmetricPivotal hsym
  let hX : SelfTransparent X := hsym X X
  let ρ := tensorPermAction X hX
  let f := permScalarTrace C p ρ
  have hz : f 0 1 = 1 := by
    change unitScalarEquiv C (p.rightTrace (((ρ 0) 1).asHom)) = 1
    rw [map_one]
    simpa only [End.one_asHom, tensorPower, rightTrace_unit] using (map_one (unitScalarEquiv C))
  have hsum : signedTraceSum (f n) =
      ∏ k ∈ Finset.range n, (pivotalDimension C p X - (k : ℂ)) :=
    signedTraceSum_falling hz (canonicalSymmetricPivotal_traceDeletion C hsym X) n
  let : Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ) := permutationCardInvertible n
  obtain ⟨Y, hY⟩ := MTC.Center.alternatingProjector_trace (ρ n) p
  have hproj := alternatingProjector_scalar_trace (C := C) (p := p) (ρ n)
  have hsum' : (∑ σ, (MTC.Center.permutationSign ℂ n σ : ℂ) *
      unitScalar C (p.rightTrace ((ρ n) σ).asHom)) =
        ∏ k ∈ Finset.range n, (pivotalDimension C p X - (k : ℂ)) := by
    simpa [signedTraceSum, f, permScalarTrace, scalarPermTrace, ← unitScalar_eq_equiv] using hsum
  have hfactor : (n.factorial : ℂ) * pivotalDimension C p Y =
      ∏ k ∈ Finset.range n, (pivotalDimension C p X - (k : ℂ)) := by
    rw [pivotalDimension, ← hY]
    exact hproj.trans hsum'
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have heq : (∏ k ∈ Finset.range n, (pivotalDimension C p X - (k : ℂ))) /
      (n.factorial : ℂ) = pivotalDimension C p Y := by
    apply (div_eq_iff hfact).2
    simpa [mul_comm] using hfactor.symm
  rw [show canonicalSymmetricPivotal hsym = p from rfl, heq]
  exact pivotalDimension_isIntegral C p Y

end MTC.Center.Normalization
end
