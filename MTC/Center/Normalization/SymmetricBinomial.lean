module
public import MTC.Center.Normalization.AlgebraicDimension
public import MTC.Center.Normalization.SymmetricPivotal
public import MTC.Center.Trace.LeftTensorTrace

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.Center.Trace

/-! # Algebraic integrality of symmetric binomials

Alternating and parity-twisted permutation projectors prove that the falling
and rising generalized binomials of a simple object’s canonical symmetric
pivotal dimension are algebraic integers.
-/

@[expose] public noncomputable section
open Equiv (Perm)
open Equiv.Perm (decomposeFin)
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

/-- The signed average of the pivotal traces of any permutation action is
an algebraic integer: it is the pivotal dimension of the image of the
alternating projector. -/
theorem alternating_projector_signed_average_isIntegral
    (p : PivotalStructure (C := C.Obj)) {Y : C.Obj} {n : ℕ}
    (ρ : Perm (Fin n) →* End Y) :
    IsIntegral ℤ ((∑ σ : Perm (Fin n), (MTC.Center.permutationSign ℂ n σ : ℂ) *
      unitScalar C (p.rightTrace (ρ σ).asHom)) / (n.factorial : ℂ)) := by
  let : Invertible (Fintype.card (Perm (Fin n)) : ℂ) := permutationCardInvertible n
  obtain ⟨Z, hZ⟩ := MTC.Center.alternatingProjector_trace ρ p
  have hproj := alternatingProjector_scalar_trace (C := C) (p := p) ρ
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have heq : (∑ σ : Perm (Fin n), (MTC.Center.permutationSign ℂ n σ : ℂ) *
      unitScalar C (p.rightTrace (ρ σ).asHom)) / (n.factorial : ℂ) =
        pivotalDimension C p Z := by
    apply (div_eq_iff hfact).2
    rw [pivotalDimension, ← hZ]
    simpa only [mul_comm] using hproj.symm
  rw [heq]
  exact pivotalDimension_isIntegral C p Z

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
  have hz : f 0 1 = 1 := permScalarTrace_zero C p ρ
  have hsum : signedTraceSum (f n) =
      ∏ k ∈ Finset.range n, (pivotalDimension C p X - (k : ℂ)) :=
    signedTraceSum_falling hz (canonicalSymmetricPivotal_traceDeletion C hsym X) n
  rw [show canonicalSymmetricPivotal hsym = p from rfl, ← hsum]
  simpa [signedTraceSum, f, permScalarTrace, scalarPermTrace, ← unitScalar_eq_equiv] using
    alternating_projector_signed_average_isIntegral C p (ρ n)


/-- Unsigned sum of a function on a finite symmetric group. -/
def unsignedTraceSum {R : Type*} [CommRing R] {n : ℕ} (F : Perm (Fin n) → R) : R :=
  ∑ σ, F σ

/-- Fixed- and moved-strand deletion yield the rising-factorial recurrence. -/
theorem unsignedTraceSum_succ {R : Type*} [CommRing R]
    {F : ∀ n : ℕ, Perm (Fin n) → R} {d : R} {n : ℕ}
    (hfixed : ∀ σ, F (n + 1) (decomposeFin.symm (0, σ)) = d * F n σ)
    (hmoved : ∀ (p : Fin (n + 1)), p ≠ 0 → ∀ σ,
      F (n + 1) (decomposeFin.symm (p, σ)) = F n σ) :
    unsignedTraceSum (F (n + 1)) = (d + (n : R)) * unsignedTraceSum (F n) := by
  rw [unsignedTraceSum, ← decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [unsignedTraceSum, hfixed, hmoved _ (Fin.succ_ne_zero _),
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Trace deletion gives the rising-factorial unsigned sum. -/
theorem unsignedTraceSum_rising {R : Type*} [CommRing R]
    {F : ∀ n : ℕ, Perm (Fin n) → R} {d : R}
    (hzero : F 0 1 = 1) (h : IsTraceDeletion F d) (n : ℕ) :
    unsignedTraceSum (F n) = ∏ k ∈ Finset.range n, (d + (k : R)) := by
  induction n with
  | zero => simp [unsignedTraceSum, hzero]
  | succ n ih =>
    simpa [ih, Finset.prod_range_succ, mul_comm] using unsignedTraceSum_succ (h.fixed n) (h.moved n)

/-- The scalar permutation sign squares to one. -/
theorem permutationSign_mul_self {n : ℕ} (σ : Perm (Fin n)) :
    (MTC.Center.permutationSign ℂ n σ : ℂ) * (MTC.Center.permutationSign ℂ n σ : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [MTC.Center.permutationSign, h]


/-- Every generalized rising binomial of a simple object's canonical
symmetric pivotal dimension is an algebraic integer. -/
theorem canonicalSymmetricPivotal_rising_binomial_isIntegral
    (X : C.Obj) [Simple X] (n : ℕ) :
    IsIntegral ℤ ((∏ k ∈ Finset.range n,
      (pivotalDimension C (canonicalSymmetricPivotal hsym) X + (k : ℂ))) / (n.factorial : ℂ)) := by
  let p := canonicalSymmetricPivotal hsym
  let hX : SelfTransparent X := hsym X X
  let ρ := tensorPermAction X hX
  let f := permScalarTrace C p ρ
  have hz : f 0 1 = 1 := permScalarTrace_zero C p ρ
  have hsum : unsignedTraceSum (f n) =
      ∏ k ∈ Finset.range n, (pivotalDimension C p X + (k : ℂ)) :=
    unsignedTraceSum_rising hz (canonicalSymmetricPivotal_traceDeletion C hsym X) n
  let ρ' := parityPermAction C.Obj hX true n
  have hsum' : (∑ σ, (MTC.Center.permutationSign ℂ n σ : ℂ) *
      unitScalar C (p.rightTrace (ρ' σ).asHom)) =
        ∏ k ∈ Finset.range n, (pivotalDimension C p X + (k : ℂ)) := by
    rw [← hsum]
    unfold unsignedTraceSum
    apply Finset.sum_congr rfl
    intro σ hσ
    have hpar : unitScalar C (p.rightTrace (ρ' σ).asHom) =
        (MTC.Center.permutationSign ℂ n σ : ℂ) * f n σ := by
      simpa [ρ', f, ρ, permScalarTrace, scalarPermTrace, ← unitScalar_eq_equiv] using
        scalarPermTrace_parity p (unitScalarEquiv C).toLinearMap hX σ
    rw [hpar, ← mul_assoc, permutationSign_mul_self, one_mul]
  rw [show canonicalSymmetricPivotal hsym = p from rfl, ← hsum']
  exact alternating_projector_signed_average_isIntegral C p ρ'


end MTC.Center.Normalization
end
