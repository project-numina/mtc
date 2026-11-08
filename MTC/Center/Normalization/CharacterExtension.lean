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

/-- A positive real value of a character of a finite group is one. -/
theorem character_eq_one_of_positive {A : Type*} [Group A] [Finite A]
    (η : A →* ℂˣ) (a : A) {r : ℝ} (hr : 0 < r) (hval : (η a : ℂ) = r) :
    η a = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite a).exists_pow_eq_one
  have hz : (r : ℂ) ^ n = 1 := by
    have h := congrArg (fun b : A => (η b : ℂ)) hpow
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one, hval] using h
  have hrpow : r ^ n = 1 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow, Complex.ofReal_one] using hz
  have hrone := (pow_eq_one_iff_of_nonneg hr.le (ne_of_gt hn)).mp hrpow
  apply Units.ext
  simpa [hrone] using hval

/-- The positivity-on-the-kernel form of the finite abelian extension step. -/
theorem character_extend_along_of_positive_kernel
    {A B : Type*} [Group A] [Finite A] [CommGroup B] [Finite B]
    (φ : A →* B) (η : A →* ℂˣ)
    (hpositive : ∀ a ∈ φ.ker, ∃ r : ℝ, 0 < r ∧ (η a : ℂ) = r) :
    ∃ ψ : B →* ℂˣ, ψ.comp φ = η := by
  apply character_extend_along φ η
  intro a ha
  obtain ⟨r, hr, hval⟩ := hpositive a ha
  exact MonoidHom.mem_ker.mpr (character_eq_one_of_positive η a hr hval)

end MTC.Center.Normalization
end
