module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import PropertyF.Definitions
public import PropertyF.BlockTrace

/-!
# Unitary blocks for braid images

A finite group representation preserves an averaged positive definite form. Its image
algebra has a matrix-block presentation in which the group acts unitarily.
-/

@[expose] public noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace PropertyF.Ground.Calculus

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
variable (ρ : G →* (Matrix ι ι ℂ)ˣ)

/-- The Gram matrix of the sum of all pullbacks of the standard form. -/
def averagedGram : Matrix ι ι ℂ :=
  ∑ g : G, (↑(ρ g) : Matrix ι ι ℂ)ᴴ * (↑(ρ g) : Matrix ι ι ℂ)

open scoped Classical in
/-- The averaged form is positive definite, even in dimension zero. -/
theorem averagedGram_posDef :
    (averagedGram ρ).PosDef :=
  Matrix.posDef_sum Finset.univ_nonempty fun g _ =>
    Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ g)))

/-- Every group element is an isometry for the averaged form. -/
theorem averagedGram_invariant (h : G) :
    (↑(ρ h) : Matrix ι ι ℂ)ᴴ * averagedGram ρ * (↑(ρ h) : Matrix ι ι ℂ) = averagedGram ρ := by
  simpa [averagedGram, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc] using
    (Equiv.sum_comp (Equiv.mulRight h) fun g => (ρ g : Matrix ι ι ℂ)ᴴ * (ρ g : Matrix ι ι ℂ))

/-! A finite complex matrix representation can be conjugated into the unitary group. -/

open scoped MatrixOrder

/-- Conjugating by a self-adjoint unit makes an isometry unitary. -/
private theorem conjugate_mem_unitary {A : Type*} [Monoid A] [StarMul A]
    (P U : Aˣ) (hP : star P = P) (h : star U * P ^ 2 * U = P ^ 2) :
    ((P * U * P⁻¹ : Aˣ) : A) ∈ unitary A :=
  (Units.mul_inv_mem_unitary (P * U) P).2 (by
    simpa only [star_mul, hP, pow_two, mul_assoc] using h)

/-- A single change of basis unitarizes every matrix in a finite group representation. -/
theorem exists_unitarizing_basis :
    ∃ P : (Matrix ι ι ℂ)ˣ, ∀ g : G,
      ((↑(P * ρ g * P⁻¹) : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ) := by
  classical
  let A := averagedGram ρ
  have hA : 0 ≤ A := (averagedGram_posDef ρ).posSemidef.nonneg
  have hS : IsUnit (CFC.sqrt A) := (CFC.isUnit_sqrt_iff A hA).2
    (averagedGram_posDef ρ).isUnit
  let P : (Matrix ι ι ℂ)ˣ := hS.unit
  have hP : (↑P : Matrix ι ι ℂ) = CFC.sqrt A := hS.unit_spec
  have hselfu : star P = P := Units.ext (by
    rw [hP]
    exact (CFC.sqrt_nonneg A).star_eq)
  have hsquare : (↑P : Matrix ι ι ℂ) * (↑P : Matrix ι ι ℂ) = A := by
    rw [hP, ← pow_two, CFC.sq_sqrt A hA]
  refine ⟨P, fun g => ?_⟩
  apply conjugate_mem_unitary P (ρ g) hselfu
  apply Units.ext
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_star,
    pow_two, hsquare, ← Matrix.star_eq_conjTranspose] using averagedGram_invariant ρ g

end PropertyF.Ground.Calculus

/-! Wedderburn decomposition of the linear span of a finite group image. -/

@[expose] public noncomputable section
namespace PropertyF.Ground.Calculus

variable {G A : Type*} [Group G] [Ring A] [Algebra ℂ A]
variable (ρ : G →* A)

/-- The group-algebra map associated to a representation in a complex algebra. -/
def groupAlgebraMap : MonoidAlgebra ℂ G →ₐ[ℂ] A :=
  MonoidAlgebra.lift ℂ A G ρ

/-- The complex algebra spanned by the group image. -/
def groupImageAlgebra : Subalgebra ℂ A := (groupAlgebraMap ρ).range

/-- A matrix-block presentation of a group-image algebra. -/
abbrev GroupBlockPresentation {r : ℕ} (d : Fin r → ℕ) :=
  groupImageAlgebra ρ ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩

/-- The image algebra has precisely the underlying linear span of the group image. -/
theorem groupImageAlgebra_toSubmodule :
    (groupImageAlgebra ρ).toSubmodule = Submodule.span ℂ (Set.range ρ) := by
  classical
  have h : (groupAlgebraMap ρ).toLinearMap =
      (Finsupp.linearCombination ℂ ρ).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap := by
    apply LinearMap.ext
    intro f
    change MonoidAlgebra.lift ℂ A G ρ f = Finsupp.linearCombination ℂ ρ f.coeff
    rw [MonoidAlgebra.lift_apply, Finsupp.linearCombination_apply]
  change (groupAlgebraMap ρ).toLinearMap.range = _
  rw [h, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Finsupp.range_linearCombination]

variable [Finite G]

open scoped Classical in
/-- A finite group's image algebra is semisimple, by Maschke and passage to a quotient. -/
theorem groupImageAlgebra_semisimple :
    IsSemisimpleRing (groupImageAlgebra ρ) :=
  let _ : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩ : Nat.card G ≠ 0)⟩
  RingHom.isSemisimpleRing_of_surjective (groupAlgebraMap ρ).rangeRestrict.toRingHom
    (AlgHom.rangeRestrict_surjective (groupAlgebraMap ρ))

open scoped Classical in
/-- The image algebra is finite-dimensional, even when the ambient algebra is not. -/
theorem groupImageAlgebra_finite :
    FiniteDimensional ℂ (groupImageAlgebra ρ) :=
  Module.Finite.of_surjective (groupAlgebraMap ρ).rangeRestrict.toLinearMap
    (AlgHom.rangeRestrict_surjective (groupAlgebraMap ρ))

/-- The finite group image algebra is a finite product of nonempty complex
matrix blocks. It is not assumed that the representation is faithful. -/
theorem groupImageAlgebra_blocks :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (GroupBlockPresentation ρ d) :=
  let _ := groupImageAlgebra_semisimple ρ
  let _ := groupImageAlgebra_finite ρ
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (groupImageAlgebra ρ)

end PropertyF.Ground.Calculus

/-! The actual linear span of a finite categorical braid image has matrix blocks. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]

/-- The tensor power acted on by the braid algebra at index `n`. -/
abbrev braidTensorPower (X : C) (n : ℕ) := tensorPower X (n + 2)

/-- The actual braid image acting by endomorphisms of the tensor power. -/
def braidEndRepresentation (X : C) (n : ℕ) :
    braidImage X n →* End (braidTensorPower X n) :=
  Aut.toEnd.comp (braidImage X n).subtype

/-- The subalgebra spanned by the genuine categorical braid image. -/
def braidAlgebra (X : C) (n : ℕ) : Subalgebra ℂ (End (braidTensorPower X n)) :=
  groupImageAlgebra (braidEndRepresentation X n)

/-- An equivalence from a categorical braid algebra to its matrix blocks. -/
abbrev BraidBlockPresentation {r : ℕ} (X : C) (n : ℕ) (d : Fin r → ℕ) :=
  braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩

end PropertyF.Ground.Calculus

/-! Unitary representatives for finite-group Wedderburn blocks. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.Calculus

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Conjugation by an invertible element as an algebra automorphism. -/
def unitConjugation (u : Aˣ) : A ≃ₐ[ℂ] A where
  toFun x := (u : A) * x * ↑u⁻¹
  invFun x := (↑u⁻¹ : A) * x * ↑u
  left_inv x := by simp [mul_assoc, ← Units.val_mul]
  right_inv x := by simp [mul_assoc, ← Units.val_mul]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' z := by
    simp [Algebra.commutes, mul_assoc]

variable {G : Type*} [Group G] (ρ : G →* A)

/-- The image group, regarded as units in its own linear-span algebra. -/
def groupInImage : G →* groupImageAlgebra ρ :=
  (groupAlgebraMap ρ).rangeRestrict.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

@[simp] theorem groupInImage_val (g : G) :
    (groupInImage ρ g : A) = ρ g := MonoidAlgebra.lift_of ρ g

/-- The canonical map from the categorical braid image into its span algebra. -/
abbrev braidInImage {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear ℂ C] {X : C} {n : ℕ} : braidImage X n →* braidAlgebra X n :=
  groupInImage (braidEndRepresentation X n)

/-- The braid-image algebra map has the original categorical action as its value. -/
@[simp] theorem braidInImage_val {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] [Preadditive C] [Linear ℂ C] {X : C} {n : ℕ} (g : braidImage X n) :
    (braidInImage g : End (braidTensorPower X n)) = braidEndRepresentation X n g :=
  groupInImage_val _ _

/-- A block presentation in which each represented group element is unitary. -/
abbrev IsUnitaryPresentation {r : ℕ} {d : Fin r → ℕ}
    (e : GroupBlockPresentation ρ d) : Prop :=
  ∀ g, Blocks.IsUnitary ⟨_, d⟩ (e (groupInImage ρ g))

/-- The group elements span their image algebra. -/
theorem groupInImage_span :
    Submodule.span ℂ (Set.range (groupInImage ρ)) = ⊤ := by
  classical
  apply Submodule.map_injective_of_injective (groupImageAlgebra ρ).toSubmodule.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  rw [← Set.range_comp']
  change Submodule.span ℂ (Set.range (fun g => (groupInImage ρ g : A))) = _
  simpa only [groupInImage_val] using (groupImageAlgebra_toSubmodule ρ).symm

variable [Finite G]

/-- A Wedderburn equivalence can be chosen so that every group element is
unitary in each matrix block. This choice is simultaneous for the whole group. -/
theorem groupImageAlgebra_unitary_blocks :
    ∃ (n : ℕ) (d : Fin n → ℕ) (e : GroupBlockPresentation ρ d),
      (∀ i, NeZero (d i)) ∧ IsUnitaryPresentation ρ e := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨n, d, hd, ⟨e⟩⟩ := groupImageAlgebra_blocks ρ
  let blockRep (i : Fin n) : G →* Matrix (Fin (d i)) (Fin (d i)) ℂ :=
    (Pi.evalMonoidHom _ i).comp (e.toMonoidHom.comp (groupInImage ρ))
  choose P hP using fun i : Fin n => exists_unitarizing_basis (blockRep i).toHomUnits
  let e' := e.trans (AlgEquiv.piCongrRight (fun i => unitConjugation (P i)))
  refine ⟨n, d, e', hd, fun g i => ?_⟩
  simpa [e', unitConjugation, blockRep] using hP i g

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]

/-- A unitary block presentation of the categorical braid-image algebra. -/
abbrev IsUnitaryBraidPresentation {X : C} {n r : ℕ} {d : Fin r → ℕ}
    (e : BraidBlockPresentation X n d) : Prop :=
  IsUnitaryPresentation (braidEndRepresentation X n) e

/-- Finite categorical braid images admit a simultaneous unitary block
realization of their actual endomorphism algebra. -/
theorem braidAlgebra_unitary_blocks {X : C} {n : ℕ} (h : Finite (braidImage X n)) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : BraidBlockPresentation X n d),
      (∀ i, NeZero (d i)) ∧ IsUnitaryBraidPresentation e :=
  let _ : Finite (braidImage X n) := h
  groupImageAlgebra_unitary_blocks _

end PropertyF.Ground.Calculus
