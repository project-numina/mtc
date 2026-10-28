module
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import PropertyF.Definitions
public import PropertyF.Ground.Calculus.Unitarization

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
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    change MonoidAlgebra.lift ℂ A G ρ a ∈ Submodule.span ℂ (Set.range ρ)
    rw [MonoidAlgebra.lift_apply]
    apply Submodule.sum_mem
    intro g hg
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self g))
  · apply Submodule.span_le.mpr
    rintro x ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.of ℂ G g, MonoidAlgebra.lift_of ρ g⟩

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
      Nonempty (groupImageAlgebra ρ ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  let _ := groupImageAlgebra_semisimple ρ
  let _ := groupImageAlgebra_finite ρ
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (groupImageAlgebra ρ)

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
/-- The group elements span their image algebra. -/
theorem groupInImage_span (ρ : G →* A) :
    Submodule.span ℂ (Set.range (groupInImage ρ)) = ⊤ := by
  classical
  apply Submodule.map_injective_of_injective (groupImageAlgebra ρ).toSubmodule.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  calc
    _ = Submodule.span ℂ (Set.range ρ) := by
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        refine ⟨g, ?_⟩
        change ρ g = MonoidAlgebra.lift ℂ A G ρ (MonoidAlgebra.of ℂ G g)
        exact (MonoidAlgebra.lift_of ρ g).symm
      · rintro ⟨g, rfl⟩
        refine ⟨groupInImage ρ g, ⟨g, rfl⟩, ?_⟩
        change MonoidAlgebra.lift ℂ A G ρ (MonoidAlgebra.of ℂ G g) = ρ g
        exact MonoidAlgebra.lift_of ρ g
    _ = (groupImageAlgebra ρ).toSubmodule := (groupImageAlgebra_toSubmodule ρ).symm

/-- A Wedderburn equivalence can be chosen so that every group element is
unitary in each matrix block. This choice is simultaneous for the whole group. -/
theorem groupImageAlgebra_unitary_blocks (ρ : G →* A) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (e : groupImageAlgebra ρ ≃ₐ[ℂ]
        ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ),
      (∀ i, NeZero (d i)) ∧ ∀ g i, e (groupInImage ρ g) i ∈
        Matrix.unitaryGroup (Fin (d i)) ℂ := by
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
        ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ),
      (∀ i, NeZero (d i)) ∧ ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
        Matrix.unitaryGroup (Fin (d i)) ℂ := by
  let _ : Finite (braidImage X n) := h
  exact groupImageAlgebra_unitary_blocks _

end PropertyF.Ground.Calculus
