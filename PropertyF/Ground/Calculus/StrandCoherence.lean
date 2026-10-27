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
  | 0 => λ_ (tensorPower X (n + 2))
  | k + 1 => by
      exact (α_ X (tensorPower X k) (tensorPower X (n + 2))) ≪≫
          (Iso.refl X ⊗ᵢ insertLeftPowerIso X n k)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion is one identity tensor factor, transported along
the canonical tensor-power isomorphism. -/
theorem addLeftBraidAlgebraIter_asHom (X : C) (n k : ℕ) (a : braidAlgebra X n) :
    ((addLeftBraidAlgebraIter X n k a : braidAlgebra X (n + k)) :
      End (tensorPower X ((n + k) + 2))).asHom =
      (insertLeftPowerIso X n k).inv ≫
        (tensorPower X k ◁ (a : End (tensorPower X (n + 2))).asHom) ≫
          (insertLeftPowerIso X n k).hom := by
  induction k with
  | zero =>
    simp only [addLeftBraidAlgebraIter, insertLeftPowerIso, tensorPower]
    monoidal
  | succ k ih =>
    change ((addLeftBraidAlgebra X (n + k) (addLeftBraidAlgebraIter X n k a) :
      braidAlgebra X (n + k + 1)) : End (tensorPower X ((n + k + 1) + 2))).asHom = _
    rw [addLeftBraidAlgebra_asHom, ih]
    simp only [insertLeftPowerIso, Iso.trans_hom, Iso.trans_inv, tensorIso_hom,
      tensorIso_inv, Iso.refl_hom, Iso.refl_inv, id_tensorHom, whiskerLeft_comp,
      Category.assoc, tensorPower]
    monoidal

end PropertyF.Ground.Calculus
