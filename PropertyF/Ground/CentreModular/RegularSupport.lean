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

/-- The regular-element character sum is supported only on characters agreeing
with FP dimension on every label of the fusion-closed collection. -/
theorem regular_character_sum_vanishes
    (C : BraidedFusionCategory) (B : Finset (Fin (rank C)))
    (hdual : ∀ a ∈ B, dualIndex C a ∈ B)
    (hclosed : ∀ a ∈ B, ∀ b ∈ B, ∀ k,
      fusionCoeff C a b k ≠ 0 → k ∈ B)
    (χ : Character ⟨unitIndex C, fusionCoeff C⟩)
    (a : Fin (rank C)) (ha : a ∈ B) (hne : χ.value a ≠ (fpSimple C a : ℂ)) :
    (∑ i ∈ B, (fpSimple C i : ℂ) * χ.value i) = 0 := by
  classical
  let t : ℂ := ∑ i ∈ B, (fpSimple C i : ℂ) * χ.value i
  have hbalance : χ.value a * t = (fpSimple C a : ℂ) * t := by
    calc
      _ = ∑ i ∈ B, (fpSimple C i : ℂ) * (χ.value a * χ.value i) := by
        simp only [t, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i ∈ B, ∑ k, (fusionCoeff C a i k : ℂ) *
          (fpSimple C i : ℂ) * χ.value k := by
        simp only [χ.mul_eq, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ k ∈ B, ∑ i ∈ B, (fusionCoeff C a i k : ℂ) *
          (fpSimple C i : ℂ) * χ.value k := by
        rw [Finset.sum_comm]
        symm
        apply Finset.sum_subset (Finset.subset_univ B)
        intro k _ hk
        apply Finset.sum_eq_zero
        intro i hi
        have hz : fusionCoeff C a i k = 0 := by
          by_contra hn
          exact hk (hclosed a ha i hi k hn)
        simp [hz]
      _ = ∑ k ∈ B, (fpSimple C a : ℂ) * (fpSimple C k : ℂ) * χ.value k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.sum_mul]
        have he := regular_coeff_eigenvector C B hdual hclosed a ha k hk
        have he' : (∑ i ∈ B, (fusionCoeff C a i k : ℂ) * (fpSimple C i : ℂ)) =
            (fpSimple C a : ℂ) * (fpSimple C k : ℂ) := by exact_mod_cast he
        rw [he']
      _ = _ := by
        simp only [t, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  by_contra ht
  exact hne (mul_right_cancel₀ ht hbalance)

/-- The S transform of the regular FP vector vanishes outside the numerical
S-centralizer of any dual- and fusion-closed set of simple labels. -/
theorem regular_S_transform_vanishes
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, simpleDimension C p i = (fpSimple C i : ℂ))
    (B : Finset (Fin (rank C)))
    (hdual : ∀ a ∈ B, dualIndex C a ∈ B)
    (hclosed : ∀ a ∈ B, ∀ b ∈ B, ∀ k,
      fusionCoeff C a b k ≠ 0 → k ∈ B)
    (k a : Fin (rank C)) (ha : a ∈ B)
    (hne : categoricalS C p a k ≠ simpleDimension C p a * simpleDimension C p k) :
    (∑ i ∈ B, simpleDimension C p i * categoricalS C p i k) = 0 := by
  classical
  let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  let χ : Character rules := {
    value := fun i => categoricalS C p i k / simpleDimension C p k
    unit_eq := by rw [categoricalS_symmetric C p, categoricalS_unit]; exact div_self (simpleDimension_ne_zero C p k)
    mul_eq := fun i j => categoricalS_verlinde C p i j k }
  have hne' : χ.value a ≠ (fpSimple C a : ℂ) := by
    intro h
    apply hne
    change categoricalS C p a k / simpleDimension C p k = (fpSimple C a : ℂ) at h
    rw [← hdim a] at h
    exact (div_eq_iff (simpleDimension_ne_zero C p k)).mp h
  have h := regular_character_sum_vanishes C B hdual hclosed χ a ha hne'
  have h' := congrArg (fun x : ℂ => x * simpleDimension C p k) h
  rw [Finset.sum_mul] at h'
  simp only [zero_mul] at h'
  have ht (i : Fin (rank C)) : (fpSimple C i : ℂ) * χ.value i * simpleDimension C p k =
      simpleDimension C p i * categoricalS C p i k := by
    change (fpSimple C i : ℂ) * (categoricalS C p i k / simpleDimension C p k) *
      simpleDimension C p k = _
    rw [hdim i]
    field_simp [simpleDimension_ne_zero C p k]
  simpa only [ht] using h'

end PropertyF.Ground.CentreModular
