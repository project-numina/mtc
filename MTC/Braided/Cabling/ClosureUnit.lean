module
public import MTC.Braided.Cabling.Naturality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Every braid generator on the tensor unit is trivial. -/
theorem braidGenerator_unit (n : ℕ) (i : Fin (n + 1)) :
    braidGenerator (𝟙_ C) n i = 1 := by
  induction n with
  | zero =>
    have : i = 0 := Fin.eq_zero i
    subst i
    apply Aut.ext
    apply Iso.ext
    change ((α_ (𝟙_ C) (𝟙_ C) (tensorPower (𝟙_ C) 0)).symm ≪≫
      ((β_ (𝟙_ C) (𝟙_ C)) ⊗ᵢ Iso.refl _) ≪≫ α_ _ _ _).hom = 𝟙 _
    simp [tensorIso_hom]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Aut.ext
      apply Iso.ext
      change ((α_ (𝟙_ C) (𝟙_ C) (tensorPower (𝟙_ C) (n+1))).symm ≪≫
        ((β_ (𝟙_ C) (𝟙_ C)) ⊗ᵢ Iso.refl _) ≪≫ α_ _ _ _).hom = 𝟙 _
      simp [tensorIso_hom]
    · apply Aut.ext
      apply Iso.ext
      change (Iso.refl (𝟙_ C) ⊗ᵢ (braidGenerator (𝟙_ C) n j).asIso).hom = 𝟙 _
      rw [ih j]
      simp [tensorIso_hom]

/-- The tensor unit has property F in every braided monoidal category. -/
theorem objectPropertyF_unit : ObjectPropertyF (𝟙_ C) := by
  intro n
  have h : braidImage (𝟙_ C) n = ⊥ := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      simp [braidGenerator_unit]
    · exact bot_le
  rw [h]
  infer_instance

/-- The zero tensor power has property F independently of the generator. -/
theorem objectPropertyF_tensorPower_zero (X : C) : ObjectPropertyF (tensorPower X 0) :=
  objectPropertyF_unit

/-- The first tensor power inherits property F by the right unitor. -/
theorem objectPropertyF_tensorPower_one {X : C} (hX : ObjectPropertyF X) :
    ObjectPropertyF (tensorPower X 1) :=
  objectPropertyF_of_retract (Retract.ofIso (ρ_ X)) hX

end MTC.Braided
