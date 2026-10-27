module
public import PropertyF.Ground.Modular.Characters
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Classification of normalized characters

An eigenbasis of fusion characters exhausts all normalized fusion characters.
This is the linear-algebra step in the standard Verlinde argument.
-/

@[expose] public noncomputable section
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
    fusionOperator N i χ.value = χ.value i • χ.value := by
  ext j
  change (∑ k, (N.coeff i j k : ℂ) * χ.value k) = χ.value i * χ.value j
  exact (χ.mul_eq i j).symm

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
    simp only [map_sum, map_smul]
    simp only [hb_eigen, map_smul]
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

/-- Symmetry and the S-square relation force the duality map to be an
involution, independently of categorical duality. -/
theorem dual_involutive (S : Matrix ι ι ℂ) (dual : ι → ι) (D : ℂ)
    (hD : D ≠ 0) (hsym : ∀ x y, S x y = S y x)
    (hsq : ∀ x y, ∑ z, S x z * S z y = if x = dual y then D else 0) :
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
theorem normalized_columns_linearIndependent (S : Matrix ι ι ℂ)
    (dual : ι → ι) (dimension : ι → ℂ) (D : ℂ)
    (hd : ∀ y, dimension y ≠ 0) (hD : D ≠ 0)
    (hsym : ∀ x y, S x y = S y x)
    (hsq : ∀ x y, ∑ z, S x z * S z y = if x = dual y then D else 0) :
    LinearIndependent ℂ (fun y x => S x y / dimension y) := by
  classical
  let A : Matrix ι ι ℂ := fun x y => S x y / dimension y
  let B : Matrix ι ι ℂ := fun x y => dimension x * S x (dual y) / D
  have hddual := dual_involutive S dual D hD hsym hsq
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
  have hdet := Matrix.det_ne_zero_of_right_inverse hab
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdet


/-- Construct `ModularData` using the S identities and the Verlinde character
equations. Completeness of the columns and the full Galois action are derived. -/
def modularDataOfVerlinde (rank : ℕ) (unit : Fin rank)
    (dual : Fin rank → Fin rank) (dimension : Fin rank → ℂ)
    (globalDimension : ℂ) (S : Matrix (Fin rank) (Fin rank) ℂ)
    (dimension_ne_zero : ∀ X, dimension X ≠ 0)
    (global_ne_zero : globalDimension ≠ 0)
    (global_eq : globalDimension = ∑ X, dimension X ^ 2)
    (S_symmetric : ∀ X Y, S X Y = S Y X)
    (S_unit : ∀ X, S X unit = dimension X)
    (unit_dimension : dimension unit = 1)
    (S_square : ∀ X Y, ∑ Z, S X Z * S Z Y =
      if X = dual Y then globalDimension else 0)
    (N : FusionRules (Fin rank)) (hunit : N.unit = unit)
    (verlinde : ∀ X Z Y,
      (S X Y / dimension Y) * (S Z Y / dimension Y) =
        ∑ W, (N.coeff X Z W : ℂ) * (S W Y / dimension Y)) :
    PropertyF.ModularData := by
  let columns : Fin rank → Character N := fun Y => {
    value := fun X => S X Y / dimension Y
    unit_eq := by rw [hunit, S_symmetric, S_unit]; exact div_self (dimension_ne_zero Y)
    mul_eq := fun X Z => verlinde X Z Y }
  have hlin : LinearIndependent ℂ (fun Y => (columns Y).value) :=
    normalized_columns_linearIndependent S dual dimension globalDimension
      dimension_ne_zero global_ne_zero S_symmetric S_square
  exact modularDataOfCharacters rank unit dual dimension globalDimension S
    dimension_ne_zero global_ne_zero global_eq S_symmetric S_unit unit_dimension
    S_square N columns (fun _ _ => rfl) (characters_bijective N columns hlin)

end PropertyF.Ground.Modular
