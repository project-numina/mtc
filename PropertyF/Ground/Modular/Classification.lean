module
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import PropertyF.BlockTrace
public import PropertyF.Definitions
public import PropertyF.CenterBasics
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.GroupTheory.Index

/-!
# Fusion rules, their characters, and classification of normalized S columns.
-/

@[expose] public noncomputable section

section
/-!
# Galois action on fusion characters

The integral structure constants make postcomposition by every field automorphism
of ℂ an action on fusion characters. If the normalized S-columns classify those
characters, this action yields the permutation required by `ModularData`.
The classification itself (including the Verlinde formula) is not assumed to
follow from the definitions here.
-/


open scoped BigOperators

namespace PropertyF.Ground.Modular

/-- The data needed to state the character equations. No fusion-ring axioms are
needed for the Galois action itself. -/
structure FusionRules (ι : Type*) where
  unit : ι
  coeff : ι → ι → ι → ℕ

/-- A function respects the multiplication encoded by fusion coefficients. -/
abbrev IsFusionCharacter {ι K : Type*} [Fintype ι] [Semiring K]
    (N : FusionRules ι) (χ : ι → K) : Prop :=
  ∀ i j, χ i * χ j = ∑ k, (N.coeff i j k : K) * χ k

/-- A normalized complex-valued character of integral fusion rules. -/
structure Character {ι : Type*} [Fintype ι] (N : FusionRules ι) where
  value : ι → ℂ
  unit_eq : value N.unit = 1
  mul_eq : IsFusionCharacter N value

namespace Character

variable {ι : Type*} [Fintype ι] {N : FusionRules ι}

@[ext] theorem ext {χ ψ : Character N} (h : χ.value = ψ.value) : χ = ψ := by
  cases χ; cases ψ; cases h; rfl

/-- Transport of a character along an arbitrary field automorphism. -/
def map (τ : ℂ ≃+* ℂ) (χ : Character N) : Character N where
  value i := τ (χ.value i)
  unit_eq := by rw [χ.unit_eq, map_one]
  mul_eq i j := by
    rw [← map_mul, χ.mul_eq, map_sum]
    simp only [map_mul, map_natCast]

/-- Complex automorphisms act by permutations of the character set. -/
def galoisPerm (τ : ℂ ≃+* ℂ) : Equiv.Perm (Character N) where
  toFun := map τ
  invFun := map τ.symm
  left_inv χ := by ext i; simp [map]
  right_inv χ := by ext i; simp [map]

/-- A labelling of all characters transports the Galois action to labels. -/
def galoisLabel (e : ι ≃ Character N) : (ℂ ≃+* ℂ) →* Equiv.Perm ι where
  toFun τ := e.symm.permCongr (galoisPerm τ)
  map_one' := by ext i; apply e.injective; ext j; simp [galoisPerm, map]
  map_mul' σ τ := by ext i; apply e.injective; ext j; simp [galoisPerm, map]

@[simp] theorem galoisLabel_character (e : ι ≃ Character N)
    (τ : ℂ ≃+* ℂ) (i j : ι) :
    (e (galoisLabel e τ i)).value j = τ ((e i).value j) := by
  simp [galoisLabel, galoisPerm, map]

end Character
end PropertyF.Ground.Modular

end

section
/-!
# Classification of normalized characters

An eigenbasis of fusion characters exhausts all normalized fusion characters.
This is the linear-algebra step in the standard Verlinde argument.
-/


open scoped BigOperators
open Module

namespace PropertyF.Ground.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (N : FusionRules ι)

/-- Left multiplication by a basis element, acting on column vectors. -/
def fusionOperator (i : ι) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.mulVecLin (fun j k => (N.coeff i j k : ℂ))

omit [DecidableEq ι] in
/-- A character is a simultaneous eigenvector of all fusion operators. -/
theorem character_eigenvector (χ : Character N) (i : ι) :
    fusionOperator N i χ.value = χ.value i • χ.value :=
  funext fun j ↦ (χ.mul_eq i j).symm

variable (columns : ι → Character N)

/-- A nonzero basis coordinate of an eigenvector has the corresponding eigenvalue. -/
theorem basis_eigenvalue_eq {K V : Type*} [CommSemiring K] [IsDomain K] [AddCommMonoid V] [Module K V]
    (b : Basis ι K V) (T : V →ₗ[K] V) (vals : ι → K) (v : V) (μ : K)
    (hb : ∀ j, T (b j) = vals j • b j) (hv : T v = μ • v)
    (i : ι) (hi : b.equivFun v i ≠ 0) : μ = vals i := by
  have hc : b.equivFun (T v) i = vals i * b.equivFun v i := by
    conv_lhs => rw [← b.sum_equivFun v]
    simp only [map_sum, map_smul, hb]
    simp [Finsupp.single_apply, mul_comm]
  rw [hv] at hc
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at hc
  exact mul_right_cancel₀ hi hc

/-- A basis consisting of characters classifies every character. -/
theorem characters_exhausted (b : Basis ι ℂ (ι → ℂ)) (hb : ∀ y, b y = (columns y).value)
    (χ : Character N) : ∃ y, χ = columns y := by
  classical
  obtain ⟨y, hy⟩ := Function.ne_iff.mp
    (show b.equivFun χ.value ≠ 0 from fun h ↦ by
      have hzero : χ.value = 0 := b.equivFun.injective (by simpa using h)
      simpa [hzero] using χ.unit_eq)
  refine ⟨y, Character.ext (funext fun i ↦ ?_)⟩
  exact basis_eigenvalue_eq b (fusionOperator N i) (fun j ↦ (columns j).value i)
    χ.value (χ.value i) (fun j ↦ by rw [hb, character_eigenvector])
    (character_eigenvector N χ i) y hy


/-- A linearly independent family of as many characters as labels is a
complete, duplicate-free classification. -/
theorem characters_bijective (hlin : LinearIndependent ℂ (fun y => (columns y).value)) :
    Function.Bijective columns := by
  classical
  refine ⟨fun _ _ h ↦ hlin.injective (congrArg Character.value h), fun χ ↦ ?_⟩
  let b := basisOfPiSpaceOfLinearIndependent hlin
  exact (characters_exhausted N columns b
    (fun y ↦ congrFun (coe_basisOfPiSpaceOfLinearIndependent hlin) y) χ).imp fun _ h ↦ h.symm

/-- Normalized columns satisfy the fusion-character equations. -/
abbrev HasVerlindeFormula {ι : Type*} [Fintype ι] {K : Type*} [DivisionSemiring K]
    (N : FusionRules ι) (S : Matrix ι ι K) (d : ι → K) : Prop :=
  ∀ i j y, (S i y / d y) * (S j y / d y) =
    ∑ k, (N.coeff i j k : K) * (S k y / d y)

/-- The square of an S-matrix is a scalar multiple of duality. -/
abbrev HasSSquare {R : Type*} [Semiring R] (S : Matrix ι ι R) (dual : ι → ι)
    (D : R) : Prop :=
  ∀ x y, ∑ z, S x z * S z y = if x = dual y then D else 0

/-- Symmetry and the S-square relation force the duality map to be an
involution, independently of categorical duality. -/
theorem dual_involutive {R : Type*} [CommSemiring R]
    {S : Matrix ι ι R} {dual : ι → ι} {D : R}
    (hD : D ≠ 0) (hsym : ∀ x y, S x y = S y x)
    (hsq : HasSSquare S dual D) :
    Function.Involutive dual := by
  intro y
  have hsym_sq : (∑ z, S (dual y) z * S z y) =
      ∑ z, S y z * S z (dual y) := by
    simp_rw [hsym (dual y), hsym _ y, mul_comm]
  by_contra hn
  apply hD
  simpa only [ite_eq_left rfl, ite_true, hsym_sq, hsq, ite_eq_right (Ne.symm hn)] using
    (hsq (dual y) y).symm

section NormalizedColumns
variable {K : Type*} [Field K] {S : Matrix ι ι K} {dimension : ι → K}

/-- Nonzero normalized columns of an invertible matrix are distinct. -/
theorem normalized_columns_injective (hdet : S.det ≠ 0) (hd : ∀ i, dimension i ≠ 0) :
    Function.Injective (fun j i ↦ S i j / dimension j) := fun a b h ↦
  (Matrix.linearIndependent_cols_of_det_ne_zero hdet).eq_of_smul_apply_eq_smul_apply
    (dimension b) (dimension a) a b (hd b) (funext fun x ↦ by
      simpa [mul_comm] using (div_eq_div_iff (hd a) (hd b)).mp (congrFun h x))

/-- The normalized S columns are linearly independent. The proof constructs an
explicit inverse from the S-square identity and nonzero dimensions. -/
theorem normalized_columns_linearIndependent {dual : ι → ι} {D : K}
    (hd : ∀ y, dimension y ≠ 0) (hD : D ≠ 0)
    (hsym : ∀ x y, S x y = S y x)
    (hsq : HasSSquare S dual D) :
    LinearIndependent K (fun y x => S x y / dimension y) :=
  let A : Matrix ι ι K := fun x y => S x y / dimension y
  let B : Matrix ι ι K := fun x y => dimension x * S x (dual y) / D
  Matrix.linearIndependent_cols_of_det_ne_zero (Matrix.det_ne_zero_of_right_inverse (by
    classical
    change A * B = 1
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ z, (S x z / dimension z) * (dimension z * S z (dual y) / D)) = _
    simp_rw [← mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _ (hd _)]
    rw [← Finset.sum_div, hsq, dual_involutive hD hsym hsq]
    split_ifs <;> simp [hD]))


end NormalizedColumns

end PropertyF.Ground.Modular
end
