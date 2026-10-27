module
public import PropertyF.Ground.Calculus.OverlapBound

/-! Tensor-power coherence for the concrete strand insertions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- At the level of endomorphisms, left insertion is left whiskering. -/
theorem addLeftBraidAlgebra_asHom (X : C) (n : ℕ) (a : braidAlgebra X n) :
    ((addLeftBraidAlgebra X n a : braidAlgebra X (n + 1)) :
      End (tensorPower X ((n + 1) + 2))).asHom =
      X ◁ (a : End (tensorPower X (n + 2))).asHom := by
  rfl

/-- At the level of endomorphisms, right insertion is right whiskering,
transported across the append isomorphism. -/
theorem addRightBraidAlgebra_asHom (X : C) (n : ℕ) (a : braidAlgebra X n) :
    ((addRightBraidAlgebra X n a : braidAlgebra X (n + 1)) :
      End (tensorPower X ((n + 1) + 2))).asHom =
      (appendIso X (n + 2)).inv ≫ ((a : End (tensorPower X (n + 2))).asHom ▷ X) ≫
        (appendIso X (n + 2)).hom := by
  rfl

/-- Canonical left insertion isomorphism, indexed by the braid-algebra
convention that index `n` has `n+2` strands. -/
def insertLeftPowerIso (X : C) (n : ℕ) : ∀ k, tensorPower X k ⊗ tensorPower X (n + 2) ≅
    tensorPower X ((n + k) + 2)
  | 0 => by simpa [tensorPower] using (λ_ (tensorPower X (n + 2)))
  | k + 1 => by
      have h : (n + (k + 1)) + 2 = ((n + k) + 2) + 1 := by omega
      rw [h]
      exact (α_ X (tensorPower X k) (tensorPower X (n + 2))) ≪≫
          (Iso.refl X ⊗ᵢ insertLeftPowerIso X n k)

end PropertyF.Ground.Calculus
