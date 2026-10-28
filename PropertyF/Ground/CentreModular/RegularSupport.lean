module
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Fusion.Agreement

/-! Fourier support of the FP-weighted regular element of a fusion-closed
collection of simple labels. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
open Modular

/-- The FP-weighted regular element of a dual-closed fusion-closed collection
is an eigenvector for multiplication by each of its labels. -/
theorem regular_coeff_eigenvector
    (C : BraidedFusionCategory) (B : Finset (Fin (rank C)))
    (hdual : ∀ a ∈ B, dualIndex C a ∈ B)
    (hclosed : ∀ a ∈ B, ∀ b ∈ B, ∀ k,
      fusionCoeff C a b k ≠ 0 → k ∈ B)
    (a : Fin (rank C)) (ha : a ∈ B) (k : Fin (rank C)) (hk : k ∈ B) :
    (∑ i ∈ B, (fusionCoeff C a i k : ℝ) * fpSimple C i) =
      fpSimple C a * fpSimple C k := by
  classical
  simp_rw [fusionCoeff_dual_adjoint C a]
  calc
    _ = ∑ i, (fusionCoeff C (dualIndex C a) k i : ℝ) * fpSimple C i := by
      apply Finset.sum_subset (Finset.subset_univ B)
      intro i _ hi
      have hz : fusionCoeff C (dualIndex C a) k i = 0 := by
        by_contra hn
        exact hi (hclosed (dualIndex C a) (hdual a ha) k hk i hn)
      simp [hz]
    _ = fpSimple C (dualIndex C a) * fpSimple C k := (fpSimple_mul C _ _).symm
    _ = _ := by rw [fpSimple_dual]

end PropertyF.Ground.CentreModular
