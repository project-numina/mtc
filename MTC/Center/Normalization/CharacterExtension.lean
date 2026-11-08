module
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Character extension for pivotal normalization

The group-theoretic step in the normalization lemma: a character trivial on
the kernel of a map into a finite abelian group factors and extends.
This file does not construct universal gradings or pivotal twists.
-/

@[expose] public noncomputable section
namespace MTC.Center.Normalization

/-- A complex character that is trivial on the kernel of a homomorphism to a
finite abelian group extends along that homomorphism. -/
theorem character_extend_along {A B : Type*} [Group A] [CommGroup B] [Finite B]
    (φ : A →* B) (η : A →* ℂˣ) (hker : φ.ker ≤ η.ker) :
    ∃ ψ : B →* ℂˣ, ψ.comp φ = η := by
  let ηbar : φ.range →* ℂˣ :=
    (QuotientGroup.lift φ.ker η hker).comp (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective (M := ℂ) φ.range ηbar
  refine ⟨ψ, ?_⟩
  apply DFunLike.ext
  intro a
  change ψ (φ a) = η a
  have h := DFunLike.congr_fun hψ (φ.rangeRestrict a)
  change ψ (φ a) = ηbar (φ.rangeRestrict a) at h
  rw [h]
  change (QuotientGroup.lift φ.ker η hker)
    ((QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict a)) = η a
  have heq : (QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict a) =
      QuotientGroup.mk a := by
    apply (QuotientGroup.quotientKerEquivRange φ).injective
    change (QuotientGroup.quotientKerEquivRange φ)
      ((QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict a)) = φ.rangeRestrict a
    exact (QuotientGroup.quotientKerEquivRange φ).apply_symm_apply _
  rw [heq]
  rfl

end MTC.Center.Normalization
end
