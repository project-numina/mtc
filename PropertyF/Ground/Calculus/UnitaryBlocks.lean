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

/-! A finite group representation preserves a positive definite Hermitian form.
The unnormalized average avoids dividing by the group order. -/

@[expose] public noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace PropertyF.Ground.Calculus

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of the sum of all pullbacks of the standard form. -/
def averagedGram (ρ : G →* (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ :=
  ∑ g : G, (↑(ρ g) : Matrix ι ι ℂ)ᴴ * (↑(ρ g) : Matrix ι ι ℂ)

/-- The averaged form is positive definite, even in dimension zero. -/
theorem averagedGram_posDef (ρ : G →* (Matrix ι ι ℂ)ˣ) :
    (averagedGram ρ).PosDef := by
  classical
  unfold averagedGram
  apply Matrix.posDef_sum Finset.univ_nonempty
  intro g _
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ g)))

/-- Every group element is an isometry for the averaged form. -/
theorem averagedGram_invariant (ρ : G →* (Matrix ι ι ℂ)ˣ) (h : G) :
    (↑(ρ h) : Matrix ι ι ℂ)ᴴ * averagedGram ρ * (↑(ρ h) : Matrix ι ι ℂ) = averagedGram ρ := by
  classical
  simpa only [averagedGram, Matrix.mul_sum, Matrix.sum_mul, Equiv.coe_mulRight, map_mul,
    Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
    (Equiv.sum_comp (Equiv.mulRight h)
      (fun g => (↑(ρ g) : Matrix ι ι ℂ)ᴴ * (↑(ρ g) : Matrix ι ι ℂ)))

end PropertyF.Ground.Calculus

/-! A finite complex matrix representation can be conjugated into the unitary group. -/

@[expose] public noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace PropertyF.Ground.Calculus

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- A single change of basis unitarizes every matrix in a finite group representation. -/
theorem exists_unitarizing_basis (ρ : G →* (Matrix ι ι ℂ)ˣ) :
    ∃ P : (Matrix ι ι ℂ)ˣ, ∀ g : G,
      ((↑(P * ρ g * P⁻¹) : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ) := by
  classical
  let A := averagedGram ρ
  have hA : 0 ≤ A := (averagedGram_posDef ρ).posSemidef.nonneg
  have hS : IsUnit (CFC.sqrt A) := (CFC.isUnit_sqrt_iff A hA).2
    (averagedGram_posDef ρ).isUnit
  let P : (Matrix ι ι ℂ)ˣ := hS.unit
  have hP : (↑P : Matrix ι ι ℂ) = CFC.sqrt A := hS.unit_spec
  have hself : star (↑P : Matrix ι ι ℂ) = ↑P := by
    rw [hP]
    exact (CFC.sqrt_nonneg A).star_eq
  have hsquare : (↑P : Matrix ι ι ℂ) * (↑P : Matrix ι ι ℂ) = A := by
    rw [hP, ← pow_two, CFC.sq_sqrt A hA]
  refine ⟨P, fun g => ?_⟩
  apply Matrix.mem_unitaryGroup_iff'.2
  have hinv : (↑(ρ g) : Matrix ι ι ℂ)ᴴ * A * (↑(ρ g) : Matrix ι ι ℂ) = A :=
    averagedGram_invariant ρ g
  change star ((↑P : Matrix ι ι ℂ) * (↑(ρ g) : Matrix ι ι ℂ) * (↑(P⁻¹) : Matrix ι ι ℂ)) *
    ((↑P : Matrix ι ι ℂ) * (↑(ρ g) : Matrix ι ι ℂ) * (↑(P⁻¹) : Matrix ι ι ℂ)) = 1
  simp only [star_mul, hself, ← Matrix.star_eq_conjTranspose] at hinv ⊢
  have hselfu : star P = P := Units.ext hself
  have hselfinv : star (↑(P⁻¹) : Matrix ι ι ℂ) = ↑(P⁻¹) := by
    have h : star (P⁻¹) = P⁻¹ := by simp [hselfu]
    exact congrArg (fun Q : (Matrix ι ι ℂ)ˣ => (↑Q : Matrix ι ι ℂ)) h
  rw [hselfinv]
  calc
    _ = (↑(P⁻¹) : Matrix ι ι ℂ) * (star (↑(ρ g) : Matrix ι ι ℂ) * A * ↑(ρ g)) * ↑(P⁻¹) := by
      rw [← hsquare]
      noncomm_ring
    _ = (↑(P⁻¹) : Matrix ι ι ℂ) * (↑P * ↑P) * ↑(P⁻¹) := by rw [hinv, hsquare]
    _ = 1 := by
      change (↑(P⁻¹ * (P * P) * P⁻¹) : Matrix ι ι ℂ) = ↑(1 : (Matrix ι ι ℂ)ˣ)
      congr 1
      simp

end PropertyF.Ground.Calculus

/-! Wedderburn decomposition of the linear span of a finite group image. -/

@[expose] public noncomputable section
namespace PropertyF.Ground.Calculus

variable {G A : Type*} [Group G] [Finite G] [Ring A] [Algebra ℂ A]

/-- The group-algebra map associated to a representation in a complex algebra. -/
def groupAlgebraMap (ρ : G →* A) : MonoidAlgebra ℂ G →ₐ[ℂ] A :=
  MonoidAlgebra.lift ℂ A G ρ

/-- The complex algebra spanned by the group image. -/
def groupImageAlgebra (ρ : G →* A) : Subalgebra ℂ A := (groupAlgebraMap ρ).range

omit [Finite G] in
/-- The image algebra has precisely the underlying linear span of the group image. -/
theorem groupImageAlgebra_toSubmodule (ρ : G →* A) :
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

/-- A finite group's image algebra is semisimple, by Maschke and passage to a quotient. -/
theorem groupImageAlgebra_semisimple (ρ : G →* A) :
    IsSemisimpleRing (groupImageAlgebra ρ) := by
  classical
  let _ : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩ : Nat.card G ≠ 0)⟩
  exact RingHom.isSemisimpleRing_of_surjective (groupAlgebraMap ρ).rangeRestrict.toRingHom
    (AlgHom.rangeRestrict_surjective (groupAlgebraMap ρ))

/-- The image algebra is finite-dimensional, even when the ambient algebra is not. -/
theorem groupImageAlgebra_finite (ρ : G →* A) :
    FiniteDimensional ℂ (groupImageAlgebra ρ) := by
  classical
  exact Module.Finite.of_surjective (groupAlgebraMap ρ).rangeRestrict.toLinearMap
    (AlgHom.rangeRestrict_surjective (groupAlgebraMap ρ))

/-- The finite group image algebra is a finite product of nonempty complex
matrix blocks. It is not assumed that the representation is faithful. -/
theorem groupImageAlgebra_blocks (ρ : G →* A) :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (groupImageAlgebra ρ ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, d⟩) :=
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

/-- The actual braid image acting by endomorphisms of the tensor power. -/
def braidEndRepresentation (X : C) (n : ℕ) :
    braidImage X n →* End (tensorPower X (n + 2)) :=
  Aut.toEnd.comp (braidImage X n).subtype

/-- The subalgebra spanned by the genuine categorical braid image. -/
def braidAlgebra (X : C) (n : ℕ) : Subalgebra ℂ (End (tensorPower X (n + 2))) :=
  groupImageAlgebra (braidEndRepresentation X n)

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

variable {G : Type*} [Group G] [Finite G]

/-- The image group, regarded as units in its own linear-span algebra. -/
def groupInImage (ρ : G →* A) : G →* groupImageAlgebra ρ :=
  (groupAlgebraMap ρ).rangeRestrict.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

omit [Finite G] in
@[simp] theorem groupInImage_val (ρ : G →* A) (g : G) :
    (groupInImage ρ g : A) = ρ g := by
  change MonoidAlgebra.lift ℂ A G ρ (MonoidAlgebra.of ℂ G g) = ρ g
  exact MonoidAlgebra.lift_of ρ g

/-- A block presentation in which each represented group element is unitary. -/
abbrev IsUnitaryPresentation {r : ℕ} {d : Fin r → ℕ} (ρ : G →* A)
    (e : groupImageAlgebra ρ ≃ₐ[ℂ] PropertyF.Blocks.Algebra ⟨_, d⟩) : Prop :=
  ∀ g i, e (groupInImage ρ g) i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ

omit [Finite G] in
/-- The group elements span their image algebra. -/
theorem groupInImage_span (ρ : G →* A) :
    Submodule.span ℂ (Set.range (groupInImage ρ)) = ⊤ := by
  classical
  apply Submodule.map_injective_of_injective (groupImageAlgebra ρ).toSubmodule.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  rw [← Set.range_comp']
  change Submodule.span ℂ (Set.range (fun g => (groupInImage ρ g : A))) = _
  simpa only [groupInImage_val] using (groupImageAlgebra_toSubmodule ρ).symm

/-- A Wedderburn equivalence can be chosen so that every group element is
unitary in each matrix block. This choice is simultaneous for the whole group. -/
theorem groupImageAlgebra_unitary_blocks (ρ : G →* A) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (e : groupImageAlgebra ρ ≃ₐ[ℂ]
        PropertyF.Blocks.Algebra ⟨_, d⟩),
      (∀ i, NeZero (d i)) ∧ IsUnitaryPresentation ρ e := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨n, d, hd, ⟨e⟩⟩ := groupImageAlgebra_blocks ρ
  let blockRep : ∀ i : Fin n, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ := fun i =>
    { toFun := fun g => e (groupInImage ρ g) i
      map_one' := by simp
      map_mul' := by intros; simp }
  have hu : ∀ i, ∃ P : (Matrix (Fin (d i)) (Fin (d i)) ℂ)ˣ,
      ∀ g, ((↑(P * (blockRep i).toHomUnits g * P⁻¹) :
        Matrix (Fin (d i)) (Fin (d i)) ℂ) ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :=
    fun i => exists_unitarizing_basis (blockRep i).toHomUnits
  choose P hP using hu
  let e' := e.trans (AlgEquiv.piCongrRight (fun i => unitConjugation (P i)))
  refine ⟨n, d, e', hd, fun g i => ?_⟩
  simpa [e', unitConjugation, blockRep] using hP i g

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]

/-- Finite categorical braid images admit a simultaneous unitary block
realization of their actual endomorphism algebra. -/
theorem braidAlgebra_unitary_blocks (X : C) (n : ℕ) (h : Finite (braidImage X n)) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : braidAlgebra X n ≃ₐ[ℂ]
        PropertyF.Blocks.Algebra ⟨_, d⟩),
      (∀ i, NeZero (d i)) ∧ IsUnitaryPresentation (braidEndRepresentation X n) e := by
  let _ : Finite (braidImage X n) := h
  exact groupImageAlgebra_unitary_blocks _

end PropertyF.Ground.Calculus
