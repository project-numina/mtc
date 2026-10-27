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

/-- Canonical right insertion isomorphism, built by appending one strand at
a time on the right. -/
def insertRightPowerIso (X : C) (n : ℕ) : ∀ k, tensorPower X (n + 2) ⊗ tensorPower X k ≅
    tensorPower X ((n + k) + 2)
  | 0 => ρ_ (tensorPower X (n + 2))
  | k + 1 => (Iso.refl (tensorPower X (n + 2)) ⊗ᵢ (appendIso X k).symm) ≪≫
      (α_ (tensorPower X (n + 2)) (tensorPower X k) X).symm ≪≫
      (insertRightPowerIso X n k ⊗ᵢ Iso.refl X) ≪≫ appendIso X ((n + k) + 2)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right insertion is one identity tensor factor, transported along
the canonical tensor-power isomorphism. -/
theorem addRightBraidAlgebraIter_asHom (X : C) (n k : ℕ) (a : braidAlgebra X n) :
    ((addRightBraidAlgebraIter X n k a : braidAlgebra X (n + k)) :
      End (tensorPower X ((n + k) + 2))).asHom =
      (insertRightPowerIso X n k).inv ≫
        ((a : End (tensorPower X (n + 2))).asHom ▷ tensorPower X k) ≫
          (insertRightPowerIso X n k).hom := by
  induction k with
  | zero =>
    simp only [addRightBraidAlgebraIter, insertRightPowerIso, tensorPower]
    monoidal
  | succ k ih =>
    change ((addRightBraidAlgebra X (n + k) (addRightBraidAlgebraIter X n k a) :
      braidAlgebra X (n + k + 1)) : End (tensorPower X ((n + k + 1) + 2))).asHom = _
    rw [addRightBraidAlgebra_asHom, ih]
    simp only [insertRightPowerIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
      tensorHom_id, comp_whiskerRight, Category.assoc]
    simp only [id_tensorHom, whisker_exchange_assoc]
    rw [← associator_naturality_left_assoc]
    simp

end PropertyF.Ground.Calculus
