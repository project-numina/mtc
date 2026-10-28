module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Analysis.Complex.Basic

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

/-- Conjugation of exact cyclotomic coefficients sends the generator to its
inverse and fixes rational numbers. -/
noncomputable def cyclotomicConj (n : ℕ) [NeZero n] :
    ExactCyclotomic n →+* ExactCyclotomic n :=
  AdjoinRoot.lift (AdjoinRoot.of (cyclotomic n ℚ)) (cyclotomicGenerator n)⁻¹ (by
    rw [← eval_map, map_cyclotomic]
    exact (cyclotomicGenerator_primitive n).inv.isRoot_cyclotomic (NeZero.pos n))

/-- The cyclotomic conjugation sends the generator to its inverse. -/
theorem cyclotomicConj_generator (n : ℕ) [NeZero n] :
    cyclotomicConj n (cyclotomicGenerator n) = (cyclotomicGenerator n)⁻¹ := by
  exact AdjoinRoot.lift_root _

/-- Exact cyclotomic conjugation is an involution. -/
theorem cyclotomicConj_involutive (n : ℕ) [NeZero n] (x : ExactCyclotomic n) :
    cyclotomicConj n (cyclotomicConj n x) = x := by
  have heq : (cyclotomicConj n).comp (cyclotomicConj n) = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · ext q
      simp [cyclotomicConj]
    · change cyclotomicConj n (cyclotomicConj n (cyclotomicGenerator n)) =
        cyclotomicGenerator n
      simp only [cyclotomicConj_generator, map_inv₀, inv_inv]
  exact DFunLike.congr_fun heq x

/-- The involution on the exact field sends `ζₙ` to `ζₙ⁻¹`. -/
noncomputable instance (n : ℕ) [NeZero n] : StarRing (ExactCyclotomic n) where
  star := cyclotomicConj n
  star_involutive := cyclotomicConj_involutive n
  star_mul := by
    intro x y
    simpa only [mul_comm] using map_mul (cyclotomicConj n) x y
  star_add := by
    intro x y
    exact map_add (cyclotomicConj n) x y

/-- The standard embedding respects the cyclotomic involution and complex
conjugation. Thus exact-field unitarity agrees with complex unitarity. -/
theorem cyclotomicEmbedding_map_star (n : ℕ) [NeZero n] (x : ExactCyclotomic n) :
    cyclotomicEmbedding n (star x) = star (cyclotomicEmbedding n x) := by
  have heq : (cyclotomicEmbedding n).comp (cyclotomicConj n) =
      (starRingEnd ℂ).comp (cyclotomicEmbedding n) := by
    apply AdjoinRoot.ringHom_ext
    · ext q
      simp [cyclotomicConj, cyclotomicEmbedding]
    · change cyclotomicEmbedding n (cyclotomicConj n (cyclotomicGenerator n)) =
        star (cyclotomicEmbedding n (cyclotomicGenerator n))
      rw [cyclotomicConj_generator, map_inv₀, cyclotomicEmbedding_generator]
      exact Complex.inv_eq_conj ((Complex.isPrimitiveRoot_exp n (NeZero.ne n)).norm'_eq_one
        (NeZero.ne n))
  exact DFunLike.congr_fun heq x

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
