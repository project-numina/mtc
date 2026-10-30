module
public import MTC.Modular.CharacterStar

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
open scoped BigOperators Matrix

namespace PropertyF.Ground.Modular
variable {ι : Type*} [Fintype ι] (N : FusionRules ι) (dual : ι → ι)
variable (hdual : ∀ i j k, N.coeff i j k = N.coeff (dual i) k j)

include hdual in
/-- Different fusion characters are orthogonal for the standard Hermitian pairing. -/
theorem character_orthogonal (χ ψ : Character N) (hne : χ ≠ ψ) :
    ∑ j, starRingEnd ℂ (χ.value j) * ψ.value j = 0 := by
  by_contra hw
  apply hne
  apply Character.ext
  funext i
  let A : Matrix ι ι ℂ := fun j k ↦ N.coeff i j k
  have hχ (j k : ι) : starRingEnd ℂ (χ.value j) * starRingEnd ℂ (χ.value k) =
      ∑ l, (N.coeff j k l : ℂ) * starRingEnd ℂ (χ.value l) := by
    simpa only [map_mul, map_sum, map_natCast] using congrArg (starRingEnd ℂ) (χ.mul_eq j k)
  have hleft : (fun j ↦ starRingEnd ℂ (χ.value j)) ᵥ* A =
      χ.value i • (fun j ↦ starRingEnd ℂ (χ.value j)) := by
    rw [← Matrix.mulVec_transpose]
    change (fun j k ↦ (N.coeff i k j : ℂ)) *ᵥ (fun j ↦ starRingEnd ℂ (χ.value j)) = _
    simpa only [hdual i,
      Ground.fusion_character_dual_eq_conj (i₀ := N.unit)
        (fun a b c ↦ (hdual a c b).symm) (by simp [χ.unit_eq]) χ.mul_eq i,
      starRingEnd_apply, star_star] using Ground.fusion_character_eigenvector hχ (dual i)
  exact (Ground.eigenvalue_eq_of_dotProduct_ne_zero
    (Ground.fusion_character_eigenvector ψ.mul_eq i) hleft (by simpa [dotProduct] using hw)).symm

include hdual in
/-- Distinct normalized columns that are fusion characters are orthogonal. -/
theorem character_columns_orthogonal [DecidableEq ι] {S : Matrix ι ι ℂ} {d : ι → ℂ}
    (cols : ι → Character N) (hcols : ∀ j i, (cols j).value i = S i j / d j)
    (hdet : S.det ≠ 0) (hd : ∀ j, d j ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (d j) = d j) {a b : ι} (hab : a ≠ b) :
    ∑ x, starRingEnd ℂ (S x a) * S x b = 0 :=
  have hne : cols a ≠ cols b := fun h ↦
    hab (normalized_columns_injective hd hdet (by
      funext i
      simpa only [hcols] using congrFun (congrArg Character.value h) i))
  (div_eq_zero_iff.mp (show (∑ x, starRingEnd ℂ (S x a) * S x b) / (d a * d b) = 0 from by
    simpa only [hcols, map_div₀, hreal, div_mul_div_comm, ← Finset.sum_div] using
      character_orthogonal N dual hdual (cols a) (cols b) hne)).resolve_right
    (mul_ne_zero (hd a) (hd b))

variable (C : Ground.BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))

local notation "Sₚ" => categoricalS C p
local notation "dₚ" => simpleDimension C p

/-- Orthogonal columns and dual-conjugation force off-dual entries of the square to vanish. -/
theorem square_off_dual_of_orthogonal {J K : Type*} [Fintype J] [CommSemiring K] [StarRing K]
    (δ : J → J) (hdual : Function.Involutive δ) {S : Matrix J J K}
    (hsym : ∀ x y, S x y = S y x) (hconj : ∀ x z, S (δ x) z = star (S x z))
    (horth : ∀ {a b}, a ≠ b → ∑ z, star (S z a) * S z b = 0)
    (x y : J) (hxy : x ≠ δ y) : ∑ z, S x z * S z y = 0 := by
  simpa only [hsym _ (δ x), hconj, star_star] using horth (fun (h : δ x = y) ↦ hxy (by
    simpa only [hdual x] using congrArg δ h))

section SquareSupport
variable {R : Type*} [CommSemiring R] [IsDomain R] [DecidableEq ι]
variable (S : Matrix ι ι R) {δ : ι → ι} {u : ι} (hδ : Function.Involutive δ)
variable (hunit : δ u = u) (hcol : ∀ x, S (δ x) u = S x u) (hne : ∀ x, S x u ≠ 0)
variable (hoff : ∀ x y, x ≠ δ y → (∑ z, S x z * S z y) = 0)

omit [DecidableEq ι] in
include hδ hunit hcol hne hoff in
/-- If the square of a matrix is supported on an involution, an invariant
nonzero column forces all supported entries to agree. -/
theorem square_support_constant (x : ι) :
    (∑ z, S x z * S z (δ x)) = ∑ z, S u z * S z u := by
  let a : ι → R := fun x => ∑ z, S x z * S z (δ x)
  have hcross (x t : ι) (h : t ≠ δ x) : (∑ z, S x z * S z t) = 0 :=
    hoff x t (fun hh ↦ h (by simpa only [hδ t] using (congrArg δ hh).symm))
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

include hδ hunit hcol hne hoff in
/-- Involution support and an invariant nonzero column determine the entire square. -/
theorem square_eq_of_support :
    HasSSquare S δ (∑ z, S u z * S z u) :=
  fun x y ↦ if h : x = δ y then by
    simpa only [h, hδ y, ite_true] using square_support_constant S hδ hunit hcol hne hoff (δ y)
  else by simpa only [ite_eq_right h] using hoff x y h

end SquareSupport

variable (hp : p.IsSpherical)

include hp in
/-- Nondegeneracy, sphericality, and real dimensions imply the S-square identity. -/
theorem categoricalS_square (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    HasSSquare Sₚ (Ground.dualIndex C) (globalDimension C) := by
  have hoff := square_off_dual_of_orthogonal (Ground.dualIndex C) (Ground.dualIndex_involutive C)
    (categoricalS_symmetric C p) (categoricalS_dual_conj C p hreal)
    (character_columns_orthogonal ⟨unitIndex C, fusionCoeff C⟩ (Ground.dualIndex C)
      (fun i j k ↦ Ground.fusionCoeff_dual_symmetry C i k j) (S := Sₚ) (d := dₚ) (categoricalSCharacter C p)
      (fun _ _ ↦ rfl) hdet (simpleDimension_ne_zero C p) hreal)
  convert square_eq_of_support Sₚ (Ground.dualIndex_involutive C) (Ground.dualIndex_unit C)
    (fun i ↦ by simpa only [categoricalS_unit] using simpleDimension_dual C p hreal i)
    (fun i ↦ by simpa only [categoricalS_unit] using simpleDimension_ne_zero C p i) hoff using 1
  simp_rw [categoricalS_symmetric C p (unitIndex C), categoricalS_unit]
  simpa only [pow_two] using categorical_global_eq_sum_squares C p hp

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

variable (hp : p.IsSpherical)

include hp in
/-- Invertibility and S-square force the global dimension to be nonzero. -/
theorem globalDimension_ne_zero_of_invertibleS (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    globalDimension C ≠ 0 := fun hz ↦
  let : Nonempty (Fin (rank C)) := ⟨unitIndex C⟩
  mul_ne_zero hdet hdet (by
    have hs : Sₚ * Sₚ = 0 := by
      ext x y
      simp [Matrix.mul_apply, categoricalS_square C p hp hdet hreal, hz]
    simpa only [Matrix.det_mul, Matrix.det_zero] using congrArg Matrix.det hs)

include hp in
/-- The S-column Galois action for any nondegenerate spherical category with
real simple dimensions, without old input bundles. -/
theorem categoricalS_galois_action_of_invertibleS (hdet : (Sₚ).det ≠ 0)
    (hreal : HasRealSimpleDimensions C p) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)),
      IsGaloisColumnAction (Sₚ) (dₚ) act :=
  exists_galoisLabel_of_verlinde (simpleDimension_ne_zero C p)
    (globalDimension_ne_zero_of_invertibleS C p hp hdet hreal) (categoricalS_symmetric C p)
    (categoricalS_unit C p) (categoricalS_square C p hp hdet hreal) (categoricalS_verlinde C p)
end PropertyF.Ground.Modular
end
