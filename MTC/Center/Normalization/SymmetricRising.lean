module
public import MTC.Center.Normalization.SymmetricBinomial

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.Center.Trace

/-! # Algebraic integrality of symmetric rising binomials

Together with the falling-binomial result, this supplies the categorical
hypotheses of the arithmetic lemma in EGNO Exercise 9.9.10.
-/

@[expose] public noncomputable section
open Equiv (Perm)
open Equiv.Perm (decomposeFin)
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Center.Normalization

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

universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _)

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
  have hz : f 0 1 = 1 := by
    change unitScalarEquiv C (p.rightTrace (((ρ 0) 1).asHom)) = 1
    rw [map_one]
    simpa only [End.one_asHom, tensorPower, rightTrace_unit] using (map_one (unitScalarEquiv C))
  have hsum : unsignedTraceSum (f n) =
      ∏ k ∈ Finset.range n, (pivotalDimension C p X + (k : ℂ)) :=
    unsignedTraceSum_rising hz (canonicalSymmetricPivotal_traceDeletion C hsym X) n
  let : Invertible (Fintype.card (Perm (Fin n)) : ℂ) := permutationCardInvertible n
  let ρ' := parityPermAction C.Obj hX true n
  obtain ⟨Y, hY⟩ := MTC.Center.alternatingProjector_trace ρ' p
  have hproj := alternatingProjector_scalar_trace (C := C) (p := p) ρ'
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
  have hfactor : (n.factorial : ℂ) * pivotalDimension C p Y =
      ∏ k ∈ Finset.range n, (pivotalDimension C p X + (k : ℂ)) := by
    rw [pivotalDimension, ← hY]
    exact hproj.trans hsum'
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have heq : (∏ k ∈ Finset.range n, (pivotalDimension C p X + (k : ℂ))) /
      (n.factorial : ℂ) = pivotalDimension C p Y := by
    apply (div_eq_iff hfact).2
    simpa [mul_comm] using hfactor.symm
  rw [show canonicalSymmetricPivotal hsym = p from rfl, heq]
  exact pivotalDimension_isIntegral C p Y

end MTC.Center.Normalization
end
