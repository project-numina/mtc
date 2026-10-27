module
public import PropertyF.Ground.Calculus.GroupBlocks
public import PropertyF.Definitions

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

/-- Its underlying vector space is exactly the linear span of the braid image. -/
theorem braidAlgebra_toSubmodule (X : C) (n : ℕ) :
    (braidAlgebra X n).toSubmodule =
      Submodule.span ℂ (Set.range (braidEndRepresentation X n)) :=
  groupImageAlgebra_toSubmodule _

/-- Finite braid image implies a finite-dimensional semisimple braid algebra. -/
theorem braidAlgebra_semisimple (X : C) (n : ℕ) (h : Finite (braidImage X n)) :
    IsSemisimpleRing (braidAlgebra X n) ∧ FiniteDimensional ℂ (braidAlgebra X n) := by
  let _ : Finite (braidImage X n) := h
  exact ⟨groupImageAlgebra_semisimple _, groupImageAlgebra_finite _⟩

/-- The actual categorical braid algebra is a finite product of complex matrix
blocks. Compatibility with spherical traces and adjoints is a further theorem. -/
theorem braidAlgebra_blocks (X : C) (n : ℕ) (h : Finite (braidImage X n)) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  let _ : Finite (braidImage X n) := h
  exact groupImageAlgebra_blocks _

end PropertyF.Ground.Calculus
