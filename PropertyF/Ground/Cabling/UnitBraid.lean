module
public import PropertyF.Ground.Cabling.Pure
public import Mathlib.Tactic
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Braiding the tensor unit with itself is the identity. -/
theorem braiding_unit_unit : (β_ (𝟙_ C) (𝟙_ C)) = Iso.refl _ := by
  apply Iso.ext
  rw [braiding_tensorUnit_left]
  monoidal

/-- The first braid generator on tensor-unit strands is trivial. -/
theorem braidGenerator_unit_zero (n : ℕ) : braidGenerator (𝟙_ C) n 0 = 1 := by
  have h : braidGenerator (𝟙_ C) n 0 = Aut.of
      ((α_ (𝟙_ C) (𝟙_ C) (tensorPower (𝟙_ C) n)).symm ≪≫
        ((β_ (𝟙_ C) (𝟙_ C)) ⊗ᵢ Iso.refl _) ≪≫
        α_ (𝟙_ C) (𝟙_ C) (tensorPower (𝟙_ C) n)) := by
    cases n <;> rfl
  rw [h]
  apply Aut.ext
  apply Iso.ext
  change ((α_ (𝟙_ C) (𝟙_ C) (tensorPower (𝟙_ C) n)).symm ≪≫
    ((β_ (𝟙_ C) (𝟙_ C)) ⊗ᵢ Iso.refl _) ≪≫
    α_ (𝟙_ C) (𝟙_ C) (tensorPower (𝟙_ C) n)).hom = 𝟙 _
  rw [braiding_unit_unit]
  simp [tensorIso_hom]

/-- Every braid generator on tensor-unit strands is trivial. -/
theorem braidGenerator_unit : ∀ (n : ℕ) (i : Fin (n + 1)),
    braidGenerator (𝟙_ C) n i = 1 := by
  intro n
  induction n with
  | zero =>
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact braidGenerator_unit_zero 0
  | succ n ih =>
    intro i
    refine Fin.cases (braidGenerator_unit_zero (n+1)) (fun j => ?_) i
    have h : braidGenerator (𝟙_ C) (n+1) j.succ =
        Aut.of (Iso.refl (𝟙_ C) ⊗ᵢ (braidGenerator (𝟙_ C) n j).asIso) := by
      rcases j with ⟨j, hj⟩
      rfl
    rw [h, ih j]
    apply Aut.ext
    apply Iso.ext
    simp [tensorIso_hom, tensorPower]

/-- The tensor unit has trivial braid image and hence property F. -/
theorem objectPropertyF_unit : ObjectPropertyF (𝟙_ C) := by
  intro n
  have h : braidImage (𝟙_ C) n = ⊥ := by
    apply le_antisymm
    · change Subgroup.closure (Set.range (braidGenerator (𝟙_ C) n)) ≤ ⊥
      apply (Subgroup.closure_le _).2
      rintro x ⟨i, rfl⟩
      simp [braidGenerator_unit]
    · exact bot_le
  rw [h]
  infer_instance
end PropertyF
