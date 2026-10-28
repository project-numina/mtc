module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Exact cyclotomic coefficients for F and R symbols

`ExactCyclotomic n` is the power-basis quotient `ℚ[X]/(Φₙ)`; for positive `n`
it is a field. Equality of represented elements reduces to polynomial
remainder modulo the monic cyclotomic polynomial. Thus a computation can
supply a polynomial remainder certificate while Lean checks the equality.

The Atlas B11-00119 symbol files use `n = 70` and power-basis degree 24. This
module defines the coefficient field and checking interface; it does not
include or assert correctness of the Atlas data.
-/

@[expose] public section
open Polynomial
namespace MTC.FRSymbols

/-- The quotient field for exact `n`th cyclotomic power-basis coefficients. -/
abbrev ExactCyclotomic (n : ℕ) := AdjoinRoot (cyclotomic n ℚ)

/-- For positive order, irreducibility of the cyclotomic polynomial gives a field. -/
noncomputable instance (n : ℕ) [NeZero n] : Field (ExactCyclotomic n) := by
  letI : Fact (Irreducible (cyclotomic n ℚ)) := ⟨cyclotomic.irreducible_rat (NeZero.pos n)⟩
  exact inferInstance

/-- The chosen class of `X` in the power-basis quotient. -/
noncomputable def cyclotomicGenerator (n : ℕ) : ExactCyclotomic n := AdjoinRoot.root (cyclotomic n ℚ)

/-- For positive order, the chosen class of `X` is a primitive root. -/
theorem cyclotomicGenerator_primitive (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (cyclotomicGenerator n) n := by
  apply (isRoot_cyclotomic_iff (R := ExactCyclotomic n)).mp
  rw [← map_cyclotomic n (AdjoinRoot.of (cyclotomic n ℚ))]
  exact AdjoinRoot.isRoot_root (cyclotomic n ℚ)

/-- The standard complex embedding sends the power-basis generator to
`exp(2πi/n)`. It fixes the complex realization used for unitary checks. -/
noncomputable def cyclotomicEmbedding (n : ℕ) [NeZero n] : ExactCyclotomic n →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℚ ℂ) (Complex.exp (2 * Real.pi * Complex.I / n)) (by
    rw [← eval_map, map_cyclotomic]
    exact (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).isRoot_cyclotomic (NeZero.pos n))

/-- The standard embedding sends the generator to the standard complex root. -/
theorem cyclotomicEmbedding_generator (n : ℕ) [NeZero n] :
    cyclotomicEmbedding n (cyclotomicGenerator n) =
      Complex.exp (2 * Real.pi * Complex.I / n) := by
  exact AdjoinRoot.lift_root _

/-- Polynomial representatives denote the same exact coefficient precisely
when their difference has zero remainder modulo the cyclotomic polynomial. -/
theorem cyclotomic_mk_eq_iff (n : ℕ) (p q : ℚ[X]) :
    AdjoinRoot.mk (cyclotomic n ℚ) p = AdjoinRoot.mk (cyclotomic n ℚ) q ↔
      (p - q) %ₘ cyclotomic n ℚ = 0 := by
  rw [AdjoinRoot.mk_eq_mk, modByMonic_eq_zero_iff_dvd (cyclotomic.monic n ℚ)]

/-- The generator is an `n`th root of unity; this also checks the `n = 70`
coefficient model used by the Atlas symbol files. -/
theorem cyclotomicGenerator_pow (n : ℕ) : cyclotomicGenerator n ^ n = 1 := by
  change (AdjoinRoot.mk (cyclotomic n ℚ) X) ^ n = 1
  have h : AdjoinRoot.mk (cyclotomic n ℚ) (X ^ n) = AdjoinRoot.mk (cyclotomic n ℚ) 1 :=
    AdjoinRoot.mk_eq_mk.mpr (by simpa using cyclotomic.dvd_X_pow_sub_one n ℚ)
  simpa only [map_pow, map_one] using h

/-- The cubic power-basis relation, a small exact cyclotomic sanity check. -/
theorem generator_three : cyclotomicGenerator 3 ^ 2 + cyclotomicGenerator 3 + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root (cyclotomic 3 ℚ)
  simpa [cyclotomicGenerator, cyclotomic_three, eval₂_add, eval₂_pow] using h

end MTC.FRSymbols
