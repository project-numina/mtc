module
public import PropertyF.Ground.Calculus.RightStrand
public import PropertyF.Ground.Calculus.ThreeBraid

/-! Two- and three-strand categorical braid embeddings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]


/-- The left three-strand generator in a chosen block presentation. -/
def tripleBlockLeft (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  b (groupInImage (braidEndRepresentation X 1) (threeGeneratorLeft X))

/-- The right three-strand generator in a chosen block presentation. -/
def tripleBlockRight (X : C) {r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X 1 ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  b (groupInImage (braidEndRepresentation X 1) (threeGeneratorRight X))

end PropertyF.Ground.Calculus
