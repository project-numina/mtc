module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Schur's lemma applied to the chosen representatives of a fusion category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators

namespace PropertyF.FusionData

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [Abelian C] [Linear ℂ C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Schur's lemma makes the simple Hom multiplicities a Kronecker delta. -/
theorem finrank_simple_hom (F : FusionData C) (i j : Fin F.rank) :
    Module.finrank ℂ (F.simpleObject i ⟶ F.simpleObject j) = if i = j then 1 else 0 := by
  classical
  letI : Simple (F.simpleObject i) := F.simple_is_simple i
  letI : Simple (F.simpleObject j) := F.simple_is_simple j
  letI : ∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y) := F.hom_finite
  rw [CategoryTheory.finrank_hom_simple_simple ℂ]
  congr 1
  exact propext ⟨F.simple_injective i j, fun h => by subst j; exact ⟨Iso.refl _⟩⟩

/-- The object dimension recovers the character value on each simple. -/
theorem fpDimension_simple (F : FusionData C) (j : Fin F.rank) :
    F.fpDimension (F.simpleObject j) = F.fpSimple j := by
  classical
  simp [fpDimension, finrank_simple_hom]

/-- Every endomorphism of a simple object is a scalar. -/
theorem simple_endomorphism_scalar (F : FusionData C) (i : Fin F.rank)
    (f : F.simpleObject i ⟶ F.simpleObject i) :
    ∃ c : ℂ, c • 𝟙 (F.simpleObject i) = f := by
  letI : Simple (F.simpleObject i) := F.simple_is_simple i
  letI : FiniteDimensional ℂ (F.simpleObject i ⟶ F.simpleObject i) := F.hom_finite _ _
  exact CategoryTheory.endomorphism_simple_eq_smul_id ℂ f

end PropertyF.FusionData
