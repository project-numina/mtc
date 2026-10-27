module
public import PropertyF.Ground.Calculus.RightStrand
public import PropertyF.Ground.Calculus.ThreeBraid

/-! Two- and three-strand categorical braid embeddings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Appending a strand to the right sends the two-strand generator to the
left three-strand generator. -/
theorem addRight_two_generator (X : C) :
    addRightStrand X 0 (imageGenerator X 0 0) = threeGeneratorLeft X := by
  apply Subtype.ext
  exact addRightAut_generator X 0 0

/-- Appending a strand to the left sends the two-strand generator to the
right three-strand generator. -/
theorem addLeft_two_generator (X : C) :
    addLeftStrand X 0 (imageGenerator X 0 0) = threeGeneratorRight X := by
  apply Subtype.ext
  change ((tensorLeft X).mapAut (tensorPower X 2)) (braidGenerator X 0 0) = braidGenerator X 1 1
  apply Aut.ext
  apply Iso.ext
  simp [Functor.mapAut, braidGenerator, tensorIso_hom, tensorLeft, id_tensorHom]

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual two-strand generator, expressed in a chosen block presentation. -/
def pairBlockGenerator (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 0 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  b (groupInImage (braidEndRepresentation X 0) (imageGenerator X 0 0))

/-- The left three-strand generator in a chosen block presentation. -/
def tripleBlockLeft (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  b (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X))

/-- The right three-strand generator in a chosen block presentation. -/
def tripleBlockRight (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  b (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X))

set_option backward.isDefEq.respectTransparency false in
/-- Right identity-strand insertion sends the squared two-strand generator
to the square of the left three-strand generator. -/
theorem rightBlockMap_pair_square (X : C) {r s : ℕ} {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X 0 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) :
    addRightBlockMap X 0 e f (pairBlockGenerator X e ^ 2) = tripleBlockLeft X f ^ 2 := by
  rw [map_pow]
  congr 1
  change f (addRightBraidAlgebra X 0 (e.symm (e (groupInImage _ _)))) = _
  rw [e.symm_apply_apply, addRightBraidAlgebra_group, addRight_two_generator]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Left identity-strand insertion sends the squared two-strand generator
to the square of the right three-strand generator. -/
theorem leftBlockMap_pair_square (X : C) {r s : ℕ} {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X 0 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) :
    addLeftBlockMap X 0 e f (pairBlockGenerator X e ^ 2) = tripleBlockRight X f ^ 2 := by
  rw [map_pow]
  congr 1
  change f (addLeftBraidAlgebra X 0 (e.symm (e (groupInImage _ _)))) = _
  rw [e.symm_apply_apply, addLeftBraidAlgebra_group, addLeft_two_generator]
  rfl

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The actual matrix-block three-strand generators satisfy the braid relation. -/
theorem tripleBlock_braid_relation (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    tripleBlockLeft X b * tripleBlockRight X b * tripleBlockLeft X b =
      tripleBlockRight X b * tripleBlockLeft X b * tripleBlockRight X b := by
  have h := three_braid_relation_map X (b.toMonoidHom.comp (groupInImage (braidEndRepresentation X 1)))
  exact h

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Finite two-strand braid image gives finite order of the squared generator
in the actual categorical block algebra. -/
theorem pairBlockGenerator_square_finite_order (X : C)
    (hfinite : Finite (braidImage X 0)) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 0 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ k : ℕ, k ≠ 0 ∧ (pairBlockGenerator X b ^ 2) ^ k = 1 := by
  have h := represented_braid_finite_order X 0 hfinite
    (b.toMonoidHom.comp (groupInImage (braidEndRepresentation X 0))) ((imageGenerator X 0 0) ^ 2)
  obtain ⟨k, hk, hp⟩ := h
  refine ⟨k, hk, ?_⟩
  change (b (groupInImage (braidEndRepresentation X 0) ((imageGenerator X 0 0) ^ 2))) ^ k = 1 at hp
  rw [map_pow, map_pow] at hp
  exact hp

end PropertyF.Ground.Calculus
