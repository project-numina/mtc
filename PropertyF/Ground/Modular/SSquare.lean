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

local notation "Sₚ" => categoricalS C p
local notation "dₚ" => simpleDimension C p

/-- A nondegenerate S matrix has distinct normalized columns. -/
theorem categoricalS_character_injective
    (hdet : (Sₚ).det ≠ 0) :
    Function.Injective (fun j i => Sₚ i j / dₚ j) := by
  intro a b h
  have hl := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  apply hl.eq_of_smul_apply_eq_smul_apply (dₚ b) (dₚ a)
    a b (simpleDimension_ne_zero C p b)
  funext x
  change dₚ b * Sₚ x a = dₚ a * Sₚ x b
  simpa only [mul_comm] using
    (div_eq_div_iff (simpleDimension_ne_zero C p a) (simpleDimension_ne_zero C p b)).mp
      (congrFun h x)

/-- The columns of a nondegenerate categorical S matrix are orthogonal. -/
theorem categoricalS_columns_orthogonal
    (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p)
    {a b : Fin (rank C)} (hab : a ≠ b) :
    ∑ x, starRingEnd ℂ (Sₚ x a) * Sₚ x b = 0 := by
  let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  let cols (j : Fin (rank C)) : Character rules := categoricalSCharacter C p j
  have hne : cols a ≠ cols b := by
    intro h
    apply hab
    apply categoricalS_character_injective C p hdet
    exact congrArg Character.value h
  have ho := character_orthogonal rules (Ground.dualIndex C) (fusionCoeff_dual_adjoint C)
    (cols a) (cols b) hne
  change (∑ x, starRingEnd ℂ (Sₚ x a / dₚ a) * (Sₚ x b / dₚ b)) = 0 at ho
  simp only [map_div₀, hreal, div_mul_div_comm, ← Finset.sum_div] at ho
  exact (div_eq_zero_iff).mp ho |>.resolve_right
    (mul_ne_zero (simpleDimension_ne_zero C p a) (simpleDimension_ne_zero C p b))


/-- Nondegeneracy forces the off-charge-conjugation entries of S² to vanish. -/
theorem categoricalS_square_off_dual
    (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p)
    (x y : Fin (rank C)) (hxy : x ≠ Ground.dualIndex C y) :
    ∑ z, Sₚ x z * Sₚ z y = 0 := by
  have hne : Ground.dualIndex C x ≠ y := by
    intro h
    apply hxy
    have hh := congrArg (Ground.dualIndex C) h
    simpa [Ground.dualIndex_involutive C x] using hh
  have ho := categoricalS_columns_orthogonal C p hdet hreal hne
  have hstar (z : Fin (rank C)) :
      starRingEnd ℂ (Sₚ z (Ground.dualIndex C x)) = Sₚ x z := by
    rw [categoricalS_symmetric C p z, categoricalS_dual_conj C p hreal]
    simp
  simpa only [hstar] using ho


/-- If the square of a matrix is supported on an involution, an invariant
nonzero column forces all supported entries to agree. -/
theorem square_support_constant {R : Type*} [CommRing R] [IsDomain R] [DecidableEq ι]
    (S : Matrix ι ι R) {δ : ι → ι} {u : ι} (hdual : Function.Involutive δ)
    (hunit : δ u = u) (hcol : ∀ x, S (δ x) u = S x u)
    (hne : ∀ x, S x u ≠ 0)
    (hoff : ∀ x y, x ≠ δ y → (∑ z, S x z * S z y) = 0) (x : ι) :
    (∑ z, S x z * S z (δ x)) = ∑ z, S u z * S z u := by
  let a : ι → R := fun x => ∑ z, S x z * S z (δ x)
  have hcross (x t : ι) (h : t ≠ δ x) : (∑ z, S x z * S z t) = 0 :=
    hoff x t (fun hh ↦ h (by simpa only [hdual t] using (congrArg δ hh).symm))
  have hleft (x : ι) :
      (∑ t, (∑ z, S x z * S z t) * S t u) = a x * S x u := by
    rw [Finset.sum_eq_single_of_mem (δ x) (Finset.mem_univ _)]
    · rw [hcol]
    · intro t _ ht
      rw [hcross x t ht, zero_mul]
  have hright (x : ι) :
      (∑ t, S x t * (∑ z, S t z * S z u)) = S x u * a u := by
    rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]
    · simp only [a, hunit]
    · intro t _ ht
      rw [hoff t u (by simpa only [hunit] using ht), mul_zero]
  have hm := congrArg (fun M : Matrix ι ι R => M x u) (Matrix.mul_assoc S S S)
  simp only [Matrix.mul_apply] at hm
  rw [hleft, hright] at hm
  have ha : a x = a u := mul_right_cancel₀ (hne x) (by simpa [mul_comm] using hm)
  simpa [a, hunit] using ha

/-- Nondegeneracy, sphericality, and real dimensions imply the S-square identity. -/
theorem categoricalS_square (hp : p.IsSpherical)
    (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    HasSSquare Sₚ (Ground.dualIndex C) (globalDimension C) := by
  classical
  intro x y
  by_cases hxy : x = Ground.dualIndex C y
  · rw [ite_eq_left hxy]
    have hy : y = Ground.dualIndex C x := by
      rw [hxy, Ground.dualIndex_involutive]
    rw [hy]
    have hs := square_support_constant Sₚ (Ground.dualIndex_involutive C)
      (Ground.dualIndex_unit C)
      (fun i => by simpa only [categoricalS_unit] using simpleDimension_dual C p hreal i)
      (fun i => by simpa only [categoricalS_unit] using simpleDimension_ne_zero C p i)
      (fun i j hij => categoricalS_square_off_dual C p hdet hreal i j hij) x
    have hu : (∑ z, Sₚ (unitIndex C) z * Sₚ z (unitIndex C)) = globalDimension C := by
      simp_rw [categoricalS_symmetric C p (unitIndex C), categoricalS_unit]
      simpa only [pow_two] using (categorical_global_eq_sum_squares C p hp).symm
    exact hs.trans hu
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

local notation "Sₚ" => categoricalS C p
local notation "dₚ" => simpleDimension C p

/-- Invertibility and S-square force the global dimension to be nonzero. -/
theorem globalDimension_ne_zero_of_invertibleS (hp : p.IsSpherical)
    (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    globalDimension C ≠ 0 := by
  classical
  let _ : Nonempty (Fin (rank C)) := ⟨unitIndex C⟩
  intro hz
  have hs : Sₚ * Sₚ = 0 := by
    ext x y
    simp [Matrix.mul_apply, categoricalS_square C p hp hdet hreal, hz]
  have hh := congrArg Matrix.det hs
  rw [Matrix.det_mul, Matrix.det_zero] at hh
  exact mul_ne_zero hdet hdet hh

/-- The S-column Galois action for any nondegenerate spherical category with
real simple dimensions, without old input bundles. -/
theorem categoricalS_galois_action_of_invertibleS (hp : p.IsSpherical)
    (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)),
      IsGaloisColumnAction (Sₚ) (dₚ) act :=
  categoricalS_galois_action C p (Ground.dualIndex C)
    (globalDimension_ne_zero_of_invertibleS C p hp hdet hreal)
    (categoricalS_square C p hp hdet hreal) (categoricalS_verlinde C p)
end PropertyF.Ground.Modular
end
