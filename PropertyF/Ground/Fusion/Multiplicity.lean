module
public import PropertyF.Ground.Fusion.Simples
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Hom-space multiplicities of finite direct sums. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

/-- The Hom space into a finite biproduct is the product of the Hom spaces. -/
def homBiproductLinearEquiv {ι : Type*} [Fintype ι] [HasFiniteBiproducts C]
    (X : C) (V : ι → C) : (X ⟶ ⨁ V) ≃ₗ[ℂ] (∀ i, X ⟶ V i) where
  toFun f i := f ≫ biproduct.π V i
  invFun f := biproduct.lift f
  left_inv f := by
    apply biproduct.hom_ext
    intro i
    simp
  right_inv f := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp
  map_smul' z f := by
    funext i
    simp

theorem finrank_hom_biproduct {ι : Type*} [Fintype ι] [HasFiniteBiproducts C]
    (X : C) (V : ι → C) [∀ i, FiniteDimensional ℂ (X ⟶ V i)] :
    Module.finrank ℂ (X ⟶ ⨁ V) = ∑ i, Module.finrank ℂ (X ⟶ V i) := by
  rw [(homBiproductLinearEquiv X V).finrank_eq, Module.finrank_pi_fintype]

/-- A chosen simple's Hom dimension counts its copies in a decomposition. -/
theorem finrank_simple_of_decomposition (D : BraidedFusionCategory.{v,u})
    (X : D.Obj) (m : Fin (rank D) → ℕ)
    (e : X ≅ ⨁ (fun p : Σ i, Fin (m i) => simples D p.1)) (i : Fin (rank D)) :
    Module.finrank ℂ (simples D i ⟶ X) = m i := by
  classical
  letI : ∀ Y Z : D.Obj, FiniteDimensional ℂ (Y ⟶ Z) := IsFusionCategory.hom_finite
  calc
    Module.finrank ℂ (simples D i ⟶ X) =
        Module.finrank ℂ (simples D i ⟶ ⨁ (fun p : Σ j, Fin (m j) => simples D p.1)) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
    _ = ∑ p : Σ j, Fin (m j), Module.finrank ℂ (simples D i ⟶ simples D p.1) :=
      finrank_hom_biproduct _ _
    _ = m i := by
      rw [Fintype.sum_sigma]
      simp [finrank_simples_hom]

/-- Every object decomposes with the canonical Hom-space multiplicities. -/
theorem exists_canonical_decomposition (D : BraidedFusionCategory.{v,u}) (X : D.Obj) :
    Nonempty (X ≅ ⨁ (fun p : Σ i : Fin (rank D),
      Fin (Module.finrank ℂ (simples D i ⟶ X)) => simples D p.1)) := by
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  have hm : (fun i => Module.finrank ℂ (simples D i ⟶ X)) = m := by
    funext i
    exact finrank_simple_of_decomposition D X m e i
  cases hm.symm
  exact ⟨e⟩

end PropertyF.Ground
