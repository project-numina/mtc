module
public import MTC.Center.Modular.TransparencyCriterion
public import MTC.Center.Induction.PivotalFusion
public import MTC.PropertyF.Pivotal.SOrthogonality

open MTC.Fusion MTC.Modular MTC.PropertyF.Reduction MTC.CategoryTheory.Dimensions
open scoped BigOperators

/-! Numerical reductions toward nondegeneracy for arbitrary pivotal structures. -/

@[expose] public noncomputable section
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- Conjugating an S entry dualizes its second label, with the pivotal
phase of the first label. No sphericality is assumed. -/
theorem categoricalS_star_eq_dual_phase (i j : Fin (rank C)) :
    starRingEnd ℂ (categoricalS C p i j) =
      (starRingEnd ℂ (simpleDimension C p i) / simpleDimension C p i) *
        categoricalS C p i (dualIndex C j) := by
  have h := fusion_character_dual_eq_conj (i₀ := unitIndex C)
    (fun a b c ↦ (fusionCoeff_dual_symmetry C a b c).symm)
    (by simp [(categoricalSCharacter C p i).unit_eq])
    (categoricalSCharacter C p i).mul_eq j
  simp only [categoricalSCharacter, normalizedSColumn,
    categoricalS_symmetric C p] at h
  have hn := simpleDimension_ne_zero C p i
  have hs : starRingEnd ℂ (simpleDimension C p i) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hn
  simp only [star_div₀] at h
  change categoricalS C p i (dualIndex C j) / simpleDimension C p i =
    starRingEnd ℂ (categoricalS C p i j) / starRingEnd ℂ (simpleDimension C p i) at h
  field_simp at h ⊢
  linear_combination -h

/-- If the unit S character is unique, its conjugate-weighted S transform
vanishes at every nonunit label. -/
theorem categoricalS_unit_character_orthogonal
    (hunique : ∀ k, k ≠ unitIndex C →
      normalizedSColumn C p k ≠ normalizedSColumn C p (unitIndex C))
    (k : Fin (rank C)) (hk : k ≠ unitIndex C) :
    ∑ i, starRingEnd ℂ (simpleDimension C p i) * categoricalS C p i k = 0 := by
  have hne : categoricalSCharacter C p (unitIndex C) ≠ categoricalSCharacter C p k := by
    intro he
    apply hunique k hk
    exact (congrArg Character.value he).symm
  have h := character_orthogonal ⟨unitIndex C, fusionCoeff C⟩ (dualIndex C)
    (fun i j k ↦ fusionCoeff_dual_symmetry C i k j)
    (categoricalSCharacter C p (unitIndex C)) (categoricalSCharacter C p k) hne
  have hd := simpleDimension_ne_zero C p k
  have hdiv : (∑ i, starRingEnd ℂ (simpleDimension C p i) * categoricalS C p i k) /
      simpleDimension C p k = 0 := by
    simpa only [categoricalSCharacter, normalizedSColumn, categoricalS_unit,
      simpleDimension_unit, div_one, ← mul_div_assoc, ← Finset.sum_div] using h
  exact (div_eq_zero_iff.mp hdiv).resolve_right hd

/-- A unique unit character gives the full conjugate-weighted Kirby identity. -/
theorem categoricalS_conjugate_kirby
    (hunique : ∀ k, k ≠ unitIndex C →
      normalizedSColumn C p k ≠ normalizedSColumn C p (unitIndex C))
    (k : Fin (rank C)) :
    (∑ i, starRingEnd ℂ (simpleDimension C p i) * categoricalS C p i k) =
      if k = unitIndex C then globalDimension C else 0 := by
  classical
  by_cases hk : k = unitIndex C
  · subst k
    simp only [categoricalS_unit]
    simpa only [simpleDimension, starRingEnd_apply, ite_true] using
      (MTC.Center.Induction.globalDimension_eq_sum_pivotal_conj_mul p).symm
  · simpa [hk] using categoricalS_unit_character_orthogonal C p hunique k hk

/-- The Hermitian Gram entry is the fusion transform of the
conjugate-weighted Kirby sum. This identity does not assume that the unit
character is unique. -/
theorem categoricalS_gram_fusion_transform (x y : Fin (rank C)) :
    (∑ i, starRingEnd ℂ (categoricalS C p i x) * categoricalS C p i y) =
      ∑ k, (fusionCoeff C (dualIndex C x) y k : ℂ) *
        (∑ i, starRingEnd ℂ (simpleDimension C p i) * categoricalS C p i k) := by
  classical
  calc
    _ = ∑ i, (starRingEnd ℂ (simpleDimension C p i) / simpleDimension C p i) *
        (categoricalS C p i (dualIndex C x) * categoricalS C p i y) := by
          simp only [categoricalS_star_eq_dual_phase, mul_assoc]
    _ = ∑ i, ∑ k, (fusionCoeff C (dualIndex C x) y k : ℂ) *
        (starRingEnd ℂ (simpleDimension C p i) * categoricalS C p i k) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [categoricalS_symmetric C p i (dualIndex C x),
            fusion_character_product (categoricalS_symmetric C p)
              (simpleDimension_ne_zero C p) (categoricalS_verlinde C p)]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [categoricalS_symmetric C p k i]
          field_simp [simpleDimension_ne_zero C p i]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- A unique unit character forces the Hermitian Gram matrix to be the
intrinsic global dimension times the identity. -/
theorem categoricalS_gram_of_unit_character_unique
    (hunique : ∀ k, k ≠ unitIndex C →
      normalizedSColumn C p k ≠ normalizedSColumn C p (unitIndex C))
    (x y : Fin (rank C)) :
    (∑ i, starRingEnd ℂ (categoricalS C p i x) * categoricalS C p i y) =
      if x = y then globalDimension C else 0 := by
  classical
  rw [categoricalS_gram_fusion_transform]
  simp_rw [categoricalS_conjugate_kirby C p hunique]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    fusionCoeff_reciprocity_labels (dualIndex C x) y (unitIndex C), fusionCoeff_unit,
    (dualIndex_involutive C).injective.eq_iff]
  split_ifs <;> simp_all

/-- An arbitrary pivotal categorical S matrix is invertible when the unit
is the only label with its normalized S character. -/
theorem categoricalS_det_ne_zero_of_unit_character_unique
    (hunique : ∀ k, k ≠ unitIndex C →
      normalizedSColumn C p k ≠ normalizedSColumn C p (unitIndex C)) :
    (categoricalS C p).det ≠ 0 := by
  classical
  let B : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
    fun x y ↦ starRingEnd ℂ (categoricalS C p y x) / globalDimension C
  have hD := MTC.Center.Induction.globalDimension_ne_zero_of_pivotal p
  apply Matrix.det_ne_zero_of_left_inverse (B := B)
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ i, (starRingEnd ℂ (categoricalS C p i x) / globalDimension C) *
      categoricalS C p i y) = _
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div,
    categoricalS_gram_of_unit_character_unique C p hunique]
  split_ifs <;> simp_all

/-- It suffices for the unit to be the only label satisfying all numerical
S-centrality equations; no sphericality or dimension positivity is used. -/
theorem categoricalS_det_ne_zero_of_trivial_S_centralizer
    (htrivial : ∀ k, (∀ i, categoricalS C p i k =
      simpleDimension C p i * simpleDimension C p k) → k = unitIndex C) :
    (categoricalS C p).det ≠ 0 :=
  categoricalS_det_ne_zero_of_unit_character_unique C p fun k hk heq ↦
    hk (htrivial k fun i ↦ (div_eq_iff (simpleDimension_ne_zero C p k)).mp (by
      simpa only [normalizedSColumn, categoricalS_unit, simpleDimension_unit, div_one] using
        congrFun heq i))

end MTC.PropertyF.Pivotal
end
