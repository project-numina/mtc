module
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic

/-!
# Galois descent to integers

An integral element fixed by a Galois group is an integer.
-/

@[expose] public section
namespace PropertyF

/-- The last arithmetic step in Theorem 1.1. For a Galois dimension field,
invariance of an algebraic integer under all Galois automorphisms forces
it to be an integer. Both descent to ℚ and integrally closedness of ℤ are proved
by Mathlib; neither is a new axiom here. -/
theorem integer_of_galois_fixed {K : Type*} [Field K] [Algebra ℚ K]
    [IsGalois ℚ K] {x : K}
    (hx : IsIntegral ℤ x) (hfixed : ∀ σ : K ≃ₐ[ℚ] K, σ x = x) :
    ∃ z : ℤ, x = (z : K) :=
  let ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfixed
  let ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (show IsIntegral ℤ q from (isIntegral_algebraMap_iff (B := K)).mp (by simpa [hq] using hx))
  ⟨z, by rw [← hq, ← hz]; simp⟩

end PropertyF
