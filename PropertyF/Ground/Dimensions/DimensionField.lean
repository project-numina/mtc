module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Extension of complex automorphisms

Automorphisms of complex subfields extend to automorphisms of ℂ. -/

@[expose] public noncomputable section
namespace PropertyF.Ground.Dimensions

/-- Every automorphism of a subfield of ℂ extends to an automorphism of ℂ.
Choose a transcendence basis, apply the automorphism to coefficients while
fixing the basis, and extend across the algebraic closure. -/
theorem extend_complex_automorphism (K : Subfield ℂ) (σ : K ≃+* K) :
    ∃ τ : ℂ ≃+* ℂ, ∀ x : K, τ (x : ℂ) = (σ x : ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  let v : s → ℂ := fun x => x
  let A := Algebra.adjoin K (Set.range v)
  let e : MvPolynomial s K ≃ₐ[K] A := hs.1.aevalEquiv
  let α : A ≃+* A := e.toRingEquiv.symm.trans
    ((MvPolynomial.mapEquiv s σ).trans e.toRingEquiv)
  let : IsAlgClosure A ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let τ : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ α
  refine ⟨τ, fun x => ?_⟩
  have hx : τ (algebraMap A ℂ (algebraMap K A x)) =
      algebraMap A ℂ (α (algebraMap K A x)) :=
    IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ α _
  have he : α (algebraMap K A x) = algebraMap K A (σ x) := by
    apply e.symm.injective
    simp [α, e]
  simpa [he, Subfield.algebraMap_ofSubfield] using hx

end PropertyF.Ground.Dimensions
