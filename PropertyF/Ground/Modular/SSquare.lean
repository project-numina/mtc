module
public import PropertyF.Ground.Modular.CharacterStar

/-!
# Orthogonality and the S-square identity

Distinct fusion characters are orthogonal by the dual-adjoint fusion rule.
For a spherical category with real simple dimensions and invertible S, the
normalized S columns are distinct, and their orthogonality gives the off-dual
part of S². Associativity of matrix multiplication and the nonzero unit column
show the remaining entries equal the global dimension.
-/
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
variable {ι : Type*} [Fintype ι] (N : FusionRules ι) (dual : ι → ι)
variable (hdual : ∀ i j k, N.coeff i j k = N.coeff (dual i) k j)

include hdual in
/-- Different fusion characters are orthogonal for the standard Hermitian pairing. -/
theorem character_orthogonal (χ ψ : Character N) (hne : χ ≠ ψ) :
    ∑ j, starRingEnd ℂ (χ.value j) * ψ.value j = 0 := by
  let w : ℂ := ∑ j, starRingEnd ℂ (χ.value j) * ψ.value j
  have hbalance (i : ι) : ψ.value i * w = χ.value i * w := by
    have hc := character_dual_conj N dual hdual χ i
    have hc' : starRingEnd ℂ (χ.value (dual i)) = χ.value i := by rw [hc]; simp
    calc
      _ = ∑ j, starRingEnd ℂ (χ.value j) * (ψ.value i * ψ.value j) := by
        simp only [w, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, ∑ k, starRingEnd ℂ (χ.value j) * ((N.coeff i j k : ℂ) * ψ.value k) := by
        simp only [ψ.mul_eq, Finset.mul_sum]
      _ = ∑ k, ∑ j, ((N.coeff (dual i) k j : ℂ) * starRingEnd ℂ (χ.value j)) * ψ.value k := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        rw [hdual i j k]
        ring
      _ = ∑ k, starRingEnd ℂ (χ.value (dual i) * χ.value k) * ψ.value k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [χ.mul_eq, map_sum, Finset.sum_mul]
        simp only [map_mul, map_natCast]
      _ = χ.value i * w := by
        simp only [w, map_mul, hc', Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hi : ∃ i, χ.value i ≠ ψ.value i := by
    by_contra h
    push Not at h
    exact hne (Character.ext (funext h))
  obtain ⟨i, hi⟩ := hi
  by_contra hw
  exact hi (mul_right_cancel₀ hw (hbalance i)).symm

/-- A nondegenerate S matrix has distinct normalized columns. -/
theorem categoricalS_character_injective (C : Ground.BraidedFusionCategory)
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdet : (categoricalS C p).det ≠ 0) :
    Function.Injective (fun j i => categoricalS C p i j / simpleDimension C p j) := by
  intro a b h
  have hl := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  apply hl.eq_of_smul_apply_eq_smul_apply (simpleDimension C p b) (simpleDimension C p a)
    a b (simpleDimension_ne_zero C p b)
  funext x
  have hx := congrFun h x
  have hda := simpleDimension_ne_zero C p a
  have hdb := simpleDimension_ne_zero C p b
  change simpleDimension C p b * categoricalS C p x a =
    simpleDimension C p a * categoricalS C p x b
  field_simp [hda, hdb] at hx
  linear_combination hx

/-- The columns of a nondegenerate categorical S matrix are orthogonal. -/
theorem categoricalS_columns_orthogonal (C : Ground.BraidedFusionCategory)
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j)
    {a b : Fin (rank C)} (hab : a ≠ b) :
    ∑ x, starRingEnd ℂ (categoricalS C p x a) * categoricalS C p x b = 0 := by
  let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  let cols (j : Fin (rank C)) : Character rules := {
    value := fun x => categoricalS C p x j / simpleDimension C p j
    unit_eq := by rw [categoricalS_symmetric C p, categoricalS_unit]; exact div_self (simpleDimension_ne_zero C p j)
    mul_eq := fun i k => categoricalS_verlinde C p i k j }
  have hne : cols a ≠ cols b := by
    intro h
    apply hab
    apply categoricalS_character_injective C p hdet
    exact congrArg Character.value h
  have ho := character_orthogonal rules (Ground.dualIndex C) (fusionCoeff_dual_adjoint C)
    (cols a) (cols b) hne
  have hda := simpleDimension_ne_zero C p a
  have hdb := simpleDimension_ne_zero C p b
  have hsum : (∑ x, starRingEnd ℂ (categoricalS C p x a) * categoricalS C p x b) =
      (∑ x, starRingEnd ℂ (categoricalS C p x a / simpleDimension C p a) *
        (categoricalS C p x b / simpleDimension C p b)) *
        (simpleDimension C p a * simpleDimension C p b) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_div₀, hreal]
    field_simp
  rw [hsum]
  change (∑ x, starRingEnd ℂ ((cols a).value x) * (cols b).value x) * _ = 0
  rw [ho, zero_mul]


/-- The tensor unit is self-dual. -/
theorem dualIndex_unit (C : Ground.BraidedFusionCategory) :
    Ground.dualIndex C (unitIndex C) = unitIndex C := by
  have h := fusionCoeff_reciprocity_labels C (unitIndex C) (unitIndex C) (unitIndex C)
  simp only [fusionCoeff_unit, ite_true] at h
  split_ifs at h with hh
  exact hh.symm


/-- Nondegeneracy forces the off-charge-conjugation entries of S² to vanish. -/
theorem categoricalS_square_off_dual (C : Ground.BraidedFusionCategory)
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j)
    (x y : Fin (rank C)) (hxy : x ≠ Ground.dualIndex C y) :
    ∑ z, categoricalS C p x z * categoricalS C p z y = 0 := by
  have hne : Ground.dualIndex C x ≠ y := by
    intro h
    apply hxy
    have hh := congrArg (Ground.dualIndex C) h
    simpa [Ground.dualIndex_involutive C x] using hh
  have ho := categoricalS_columns_orthogonal C p hdet hreal hne
  have hstar (z : Fin (rank C)) :
      starRingEnd ℂ (categoricalS C p z (Ground.dualIndex C x)) = categoricalS C p x z := by
    rw [categoricalS_symmetric C p z, categoricalS_dual_conj C p hreal]
    simp
  simpa only [hstar] using ho


/-- Nondegeneracy, sphericality, and real dimensions imply the S-square identity. -/
theorem categoricalS_square (C : Ground.BraidedFusionCategory)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j)
    (x y : Fin (rank C)) :
    ∑ z, categoricalS C p x z * categoricalS C p z y =
      if x = Ground.dualIndex C y then globalDimension C else 0 := by
  classical
  let S := categoricalS C p
  let u := unitIndex C
  let δ := Ground.dualIndex C
  let a : Fin (rank C) → ℂ := fun x => ∑ z, S x z * S z (δ x)
  have hunit : δ u = u := dualIndex_unit C
  have hdual : Function.Involutive δ := Ground.dualIndex_involutive C
  have hcross (x t : Fin (rank C)) (h : t ≠ δ x) :
      (∑ z, S x z * S z t) = 0 := by
    apply categoricalS_square_off_dual C p hdet hreal x t
    intro hh
    apply h
    change x = δ t at hh
    have he := congrArg δ hh
    rw [hdual t] at he
    exact he.symm
  have hsunit (x : Fin (rank C)) : S x u = simpleDimension C p x := categoricalS_unit C p x
  have hleft (x : Fin (rank C)) :
      (∑ t, (∑ z, S x z * S z t) * S t u) = a x * simpleDimension C p x := by
    rw [Finset.sum_eq_single (δ x)]
    · rw [hsunit, simpleDimension_dual C p hreal]
    · intro t _ ht
      rw [hcross x t ht, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hright (x : Fin (rank C)) :
      (∑ t, S x t * (∑ z, S t z * S z u)) = simpleDimension C p x * a u := by
    rw [Finset.sum_eq_single u]
    · rw [hsunit]
      congr 1
      simp only [a, hunit]
    · intro t _ ht
      have hh : t ≠ δ u := by simpa [hunit] using ht
      rw [categoricalS_square_off_dual C p hdet hreal t u hh, mul_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hall (x : Fin (rank C)) : a x = a u := by
    have hm := congrArg (fun M : Matrix (Fin (rank C)) (Fin (rank C)) ℂ => M x u)
      (Matrix.mul_assoc S S S)
    simp only [Matrix.mul_apply] at hm
    rw [hleft, hright] at hm
    exact mul_right_cancel₀ (simpleDimension_ne_zero C p x) (by simpa [mul_comm] using hm)
  have hu : a u = globalDimension C := by
    change (∑ z, categoricalS C p (unitIndex C) z *
      categoricalS C p z (Ground.dualIndex C (unitIndex C))) = globalDimension C
    rw [dualIndex_unit C]
    simp_rw [categoricalS_symmetric C p (unitIndex C), categoricalS_unit]
    simpa only [pow_two] using (categorical_global_eq_sum_squares C p hp).symm
  by_cases hxy : x = δ y
  · rw [ite_eq_left hxy]
    have hy : y = δ x := by
      have he := congrArg δ hxy
      rw [hdual y] at he
      exact he.symm
    rw [hy]
    change a x = globalDimension C
    rw [hall, hu]
  · rw [ite_eq_right hxy]
    exact categoricalS_square_off_dual C p hdet hreal x y hxy

end PropertyF.Ground.Modular
