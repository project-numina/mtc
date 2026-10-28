module
public import PropertyF.Ground.Modular.CharacterStar

/-!
# Orthogonality, the S-square identity, and modular constructions.
-/

@[expose] public noncomputable section

section
/-!
# Orthogonality and the S-square identity

Distinct fusion characters are orthogonal by the dual-adjoint fusion rule.
For a spherical category with real simple dimensions and invertible S, the
normalized S columns are distinct, and their orthogonality gives the off-dual
part of S². Associativity of matrix multiplication and the nonzero unit column
show the remaining entries equal the global dimension.
-/
open scoped BigOperators

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
    simpa [w, hc] using character_inner_balance N dual hdual χ ψ i
  have hi : ∃ i, χ.value i ≠ ψ.value i := by
    by_contra h
    push Not at h
    exact hne (Character.ext (funext h))
  obtain ⟨i, hi⟩ := hi
  by_contra hw
  exact hi (mul_right_cancel₀ hw (hbalance i)).symm

variable (C : Ground.BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))

/-- A nondegenerate S matrix has distinct normalized columns. -/
theorem categoricalS_character_injective
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
theorem categoricalS_columns_orthogonal
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p)
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


/-- Nondegeneracy forces the off-charge-conjugation entries of S² to vanish. -/
theorem categoricalS_square_off_dual
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p)
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


/-- If the square of a matrix is supported on an involution, an invariant
nonzero column forces all supported entries to agree. -/
theorem square_support_constant [DecidableEq ι]
    (S : Matrix ι ι ℂ) {δ : ι → ι} {u : ι} (hdual : Function.Involutive δ)
    (hunit : δ u = u) (hcol : ∀ x, S (δ x) u = S x u)
    (hne : ∀ x, S x u ≠ 0)
    (hoff : ∀ x y, x ≠ δ y → (∑ z, S x z * S z y) = 0) (x : ι) :
    (∑ z, S x z * S z (δ x)) = ∑ z, S u z * S z u := by
  let a : ι → ℂ := fun x => ∑ z, S x z * S z (δ x)
  have hcross (x t : ι) (h : t ≠ δ x) : (∑ z, S x z * S z t) = 0 := by
    apply hoff x t
    intro hh
    apply h
    have he := congrArg δ hh
    rw [hdual t] at he
    exact he.symm
  have hleft (x : ι) :
      (∑ t, (∑ z, S x z * S z t) * S t u) = a x * S x u := by
    rw [Finset.sum_eq_single (δ x)]
    · rw [hcol]
    · intro t _ ht
      rw [hcross x t ht, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hright (x : ι) :
      (∑ t, S x t * (∑ z, S t z * S z u)) = S x u * a u := by
    rw [Finset.sum_eq_single u]
    · simp only [a, hunit]
    · intro t _ ht
      have hh : t ≠ δ u := by simpa [hunit] using ht
      rw [hoff t u hh, mul_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hm := congrArg (fun M : Matrix ι ι ℂ => M x u) (Matrix.mul_assoc S S S)
  simp only [Matrix.mul_apply] at hm
  rw [hleft, hright] at hm
  have ha : a x = a u := mul_right_cancel₀ (hne x) (by simpa [mul_comm] using hm)
  simpa [a, hunit] using ha

/-- Nondegeneracy, sphericality, and real dimensions imply the S-square identity. -/
theorem categoricalS_square (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p)
    (x y : Fin (rank C)) :
    ∑ z, categoricalS C p x z * categoricalS C p z y =
      if x = Ground.dualIndex C y then globalDimension C else 0 := by
  classical
  let S := categoricalS C p
  let u := unitIndex C
  let δ := Ground.dualIndex C
  let a : Fin (rank C) → ℂ := fun x => ∑ z, S x z * S z (δ x)
  have hunit : δ u = u := Ground.dualIndex_unit C
  have hdual : Function.Involutive δ := Ground.dualIndex_involutive C
  have hall (x : Fin (rank C)) : a x = a u := by
    have h := square_support_constant S hdual hunit
      (fun i => by simpa only [S, u, δ, categoricalS_unit] using simpleDimension_dual C p hreal i)
      (fun i => by simpa only [S, u, categoricalS_unit] using simpleDimension_ne_zero C p i)
      (fun i j hij => categoricalS_square_off_dual C p hdet hreal i j hij) x
    simpa only [a, hunit] using h
  have hu : a u = globalDimension C := by
    change (∑ z, categoricalS C p (unitIndex C) z *
      categoricalS C p z (Ground.dualIndex C (unitIndex C))) = globalDimension C
    rw [Ground.dualIndex_unit C]
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
end

section
/-!
# Galois symmetry from an invertible categorical S matrix

A spherical category with real simple dimensions and an invertible S matrix
has the Galois symmetries of its normalized S columns.
-/
open scoped BigOperators
open PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Modular

variable (C : Ground.BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))

/-- Invertibility and S-square force the global dimension to be nonzero. -/
theorem globalDimension_ne_zero_of_invertibleS (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    globalDimension C ≠ 0 := by
  classical
  let _ : Nonempty (Fin (rank C)) := ⟨unitIndex C⟩
  intro hz
  have hs : categoricalS C p * categoricalS C p = 0 := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.zero_apply, categoricalS_square C p hp hdet hreal, hz]
    split_ifs <;> rfl
  have hh := congrArg Matrix.det hs
  rw [Matrix.det_mul] at hh
  simp only [Matrix.det_zero] at hh
  exact mul_ne_zero hdet hdet hh

/-- The S-column Galois action for any nondegenerate spherical category with
real simple dimensions, without old input bundles. -/
theorem categoricalS_galois_action_of_invertibleS (hp : p.IsSpherical)
    (hdet : (categoricalS C p).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)), ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (categoricalS C p i j / simpleDimension C p j) =
        categoricalS C p i (act σ j) / simpleDimension C p (act σ j) :=
  categoricalS_galois_action C p (Ground.dualIndex C)
    (globalDimension_ne_zero_of_invertibleS C p hp hdet hreal)
    (categoricalS_square C p hp hdet hreal) (categoricalS_verlinde C p)
end PropertyF.Ground.Modular
end
