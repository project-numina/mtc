module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [Linear ℂ C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Schur's lemma compares any two double-dual isomorphisms of a simple object. -/
theorem doubleDualIso_scalar {X : C} [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (j k : X ≅ (Xᘁ)ᘁ) : ∃ c : ℂ, c ≠ 0 ∧ k.hom = c • j.hom ∧
    k.inv = c⁻¹ • j.inv := by
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (k.hom ≫ j.inv)
  have hhom : k.hom = c • j.hom := by
    calc
      k.hom = (k.hom ≫ j.inv) ≫ j.hom := by simp
      _ = c • j.hom := by rw [← hc]; simp
  have hc0 : c ≠ 0 := by
    intro h
    have : k.hom = 0 := by simp [h, hhom]
    have : 𝟙 X = 0 := by simpa using congrArg (fun f => f ≫ k.inv) this
    exact id_nonzero X this
  have hinv : k.inv = c⁻¹ • j.inv := by
    apply (cancel_mono k.hom).1
    simp only [Linear.smul_comp, ← Linear.comp_smul, Iso.inv_hom_id]
    rw [hhom]
    simp [hc0, smul_smul]
  exact ⟨c, hc0, hhom, hinv⟩

/-- The product of the two quantum traces on a simple object does not depend
on the chosen double-dual isomorphism. -/
theorem squaredNorm_independent {X : C} [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (j k : X ≅ (Xᘁ)ᘁ) :
    scalar (rightQuantumTrace j) * scalar (leftQuantumTrace j) =
      scalar (rightQuantumTrace k) * scalar (leftQuantumTrace k) := by
  obtain ⟨c, hc, hhom, hinv⟩ := doubleDualIso_scalar j k
  have hr : rightQuantumTrace k = c • rightQuantumTrace j := by
    apply End.homEquiv.injective
    simp [rightQuantumTrace, hhom, tensorHom_def]
  have hl : leftQuantumTrace k = c⁻¹ • leftQuantumTrace j := by
    apply End.homEquiv.injective
    simp [leftQuantumTrace, hinv, tensorHom_def]
  rw [hr, hl, map_smul, map_smul]
  simp only [smul_eq_mul]
  field_simp

end PropertyF.Ground.Dimensions
