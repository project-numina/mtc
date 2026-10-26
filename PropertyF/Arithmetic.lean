module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic

@[expose] public section
namespace PropertyF

/-- The last arithmetic step in Theorem 1.1. For a finite normal dimension
field, invariance of an algebraic integer under all Galois automorphisms forces
it to be an integer. Both descent to ℚ and integrally closedness of ℤ are proved
by Mathlib; neither is a new axiom here. -/
theorem integer_of_galois_fixed {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] {x : K}
    (hx : IsIntegral ℤ x) (hfixed : ∀ σ : K ≃ₐ[ℚ] K, σ x = x) :
    ∃ z : ℤ, x = (z : K) := by
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfixed
  have hqint : IsIntegral ℤ q := by
    apply (isIntegral_algebraMap_iff (B := K)).mp
    simpa [hq] using hx
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨z, ?_⟩
  rw [← hq, ← hz]
  simp

end PropertyF
