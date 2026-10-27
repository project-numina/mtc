module
public import PropertyF.Definitions
public import PropertyF.Transfer

/-! Reversing the braiding inverts each actual adjacent braid generator. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

theorem reverse_braidGenerator (X : C) : ∀ (n : ℕ) (i : Fin (n + 1)),
    @braidGenerator C _ _ (CategoryTheory.reverseBraiding C) X n i =
      (braidGenerator X n i)⁻¹ := by
  intro n
  induction n with
  | zero =>
    intro ⟨i, hi⟩
    have : i = 0 := by omega
    subst i
    apply CategoryTheory.Aut.ext
    apply Iso.ext
    change ((α_ X X (tensorPower X 0)).symm ≪≫
        ((β_ X X).symm ⊗ᵢ Iso.refl (tensorPower X 0)) ≪≫ α_ X X (tensorPower X 0)).hom =
      ((α_ X X (tensorPower X 0)).symm ≪≫
        ((β_ X X) ⊗ᵢ Iso.refl (tensorPower X 0)) ≪≫ α_ X X (tensorPower X 0)).inv
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, Category.assoc]
  | succ n ih =>
    intro ⟨i, hi⟩
    cases i with
    | zero =>
      apply CategoryTheory.Aut.ext
      apply Iso.ext
      change ((α_ X X (tensorPower X (n + 1))).symm ≪≫
          ((β_ X X).symm ⊗ᵢ Iso.refl (tensorPower X (n + 1))) ≪≫
            α_ X X (tensorPower X (n + 1))).hom =
        ((α_ X X (tensorPower X (n + 1))).symm ≪≫
          ((β_ X X) ⊗ᵢ Iso.refl (tensorPower X (n + 1))) ≪≫
            α_ X X (tensorPower X (n + 1))).inv
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
        tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, Category.assoc]
    | succ i =>
      apply CategoryTheory.Aut.ext
      apply Iso.ext
      simp only [braidGenerator, ih]
      simp only [Aut.inv_asIso, Iso.symm_hom, tensorIso_hom, Iso.refl_hom]
      change 𝟙 X ⊗ₘ (braidGenerator X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso.inv =
        (Iso.refl X ⊗ᵢ (braidGenerator X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso).inv
      rw [tensorIso_inv, Iso.refl_inv]

/-- Reversing the braiding leaves each actual braid image subgroup unchanged. -/
theorem reverse_braidImage (X : C) (n : ℕ) :
    @braidImage C _ _ (CategoryTheory.reverseBraiding C) X n = braidImage X n := by
  unfold braidImage
  have h : @braidGenerator C _ _ (CategoryTheory.reverseBraiding C) X n =
      fun i => (braidGenerator X n i)⁻¹ := funext (reverse_braidGenerator X n)
  rw [h]
  exact closure_inverse_generators (braidGenerator X n)

/-- Property F is invariant under braiding reversal. -/
theorem reverse_objectPropertyF_iff (X : C) :
    @ObjectPropertyF C _ _ (CategoryTheory.reverseBraiding C) X ↔ ObjectPropertyF X := by
  unfold ObjectPropertyF
  simp only [reverse_braidImage]

end PropertyF.Ground.Centre
