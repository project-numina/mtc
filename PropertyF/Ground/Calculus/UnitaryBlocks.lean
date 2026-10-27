module
public import PropertyF.Ground.Calculus.BraidBlocks
public import PropertyF.Ground.Calculus.Unitarization

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
