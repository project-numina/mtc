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

/-- A normalized complex-valued character of integral fusion rules. -/
structure Character {ι : Type*} [Fintype ι] (N : FusionRules ι) where
  value : ι → ℂ
  unit_eq : value N.unit = 1
  mul_eq : ∀ i j, value i * value j = ∑ k, (N.coeff i j k : ℂ) * value k

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

/-- A basis consisting of characters classifies every character. -/
theorem characters_exhausted (columns : ι → Character N)
    (b : Basis ι ℂ (ι → ℂ)) (hb : ∀ y, b y = (columns y).value)
    (χ : Character N) : ∃ y, χ = columns y := by
  classical
  have hcoeff : ∃ y, b.equivFun χ.value y ≠ 0 := by
    by_contra h
    push Not at h
    have heq : b.equivFun χ.value = 0 := by ext y; simp [h]
    have hzero : χ.value = 0 := b.equivFun.injective (by simpa using heq)
    have := χ.unit_eq
    rw [hzero] at this
    simp at this
  obtain ⟨y, hy⟩ := hcoeff
  have hb_eigen (i x : ι) : fusionOperator N i (b x) =
      (columns x).value i • b x := by
    rw [hb, character_eigenvector]
  have hcoord (i : ι) : b.equivFun (fusionOperator N i χ.value) y =
      (columns y).value i * b.equivFun χ.value y := by
    conv_lhs => rw [← b.sum_equivFun χ.value]
    simp only [map_sum, map_smul, hb_eigen]
    simp [Finsupp.single_apply, mul_comm]
  have heval (i : ι) : χ.value i = (columns y).value i := by
    have he := hcoord i
    rw [character_eigenvector] at he
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at he
    exact mul_right_cancel₀ hy he
  exact ⟨y, Character.ext (funext heval)⟩


/-- A linearly independent family of as many characters as labels is a
complete, duplicate-free classification. -/
theorem characters_bijective (columns : ι → Character N)
    (hlin : LinearIndependent ℂ (fun y => (columns y).value)) :
    Function.Bijective columns := by
  classical
  constructor
  · intro i j h
    apply hlin.injective
    exact congrArg Character.value h
  · intro χ
    let b := basisOfPiSpaceOfLinearIndependent hlin
    have hb : ∀ y, b y = (columns y).value := by
      intro y
      exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hlin) y
    obtain ⟨y, hy⟩ := characters_exhausted N columns b hb χ
    exact ⟨y, hy.symm⟩

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
    apply Finset.sum_congr rfl
    intro z _
    rw [hsym (dual y) z, hsym z y]
    ring
  have h := hsq (dual y) y
  rw [ite_eq_left rfl, hsym_sq, hsq] at h
  by_contra hn
  have hn' : y ≠ dual (dual y) := Ne.symm hn
  rw [ite_eq_right hn'] at h
  exact hD h.symm

/-- The normalized S columns are linearly independent. The proof constructs an
explicit inverse from the S-square identity and nonzero dimensions. -/
theorem normalized_columns_linearIndependent {K : Type*} [Field K] {S : Matrix ι ι K}
    {dual : ι → ι} {dimension : ι → K} {D : K}
    (hd : ∀ y, dimension y ≠ 0) (hD : D ≠ 0)
    (hsym : ∀ x y, S x y = S y x)
    (hsq : HasSSquare S dual D) :
    LinearIndependent K (fun y x => S x y / dimension y) := by
  classical
  let A : Matrix ι ι K := fun x y => S x y / dimension y
  let B : Matrix ι ι K := fun x y => dimension x * S x (dual y) / D
  have hddual := dual_involutive hD hsym hsq
  have hab : A * B = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ z, (S x z / dimension z) * (dimension z * S z (dual y) / D)) = _
    have hterm (z : ι) : (S x z / dimension z) *
        (dimension z * S z (dual y) / D) = (S x z * S z (dual y)) / D := by
      field_simp [hd z, hD]
    simp_rw [hterm]
    rw [← Finset.sum_div, hsq, hddual]
    split_ifs <;> simp [hD]
  exact Matrix.linearIndependent_cols_of_det_ne_zero (Matrix.det_ne_zero_of_right_inverse hab)


end PropertyF.Ground.Modular
end
