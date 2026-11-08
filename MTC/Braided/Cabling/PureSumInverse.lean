module
public import MTC.Braided.Cabling.PureSumColored

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

theorem tensor_refl_heq_of_source_eq {A B B' D : C} (f : B ≅ D) (g : B' ≅ D)
    (p : B = B') (h : HEq f g) : HEq (Iso.refl A ⊗ᵢ f) (Iso.refl A ⊗ᵢ g) := by
  cases p
  have hh : f = g := eq_of_heq h
  cases hh
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A negative crossing is the inverse positive crossing at the swapped colors. -/
theorem coloredGeneratorInverse_heq_symm : ∀ (n : ℕ) (i : Fin (n + 1))
    (X : Fin (n + 2) → C),
    HEq (coloredGeneratorInverse n i X)
      (coloredGenerator n i (fun j => X (coloredSwap n i j))).symm := by
  intro n
  induction n with
  | zero =>
    intro i X
    fin_cases i
    change HEq ((α_ (X 0) (X 1) (𝟙_ C)).symm ≪≫
      ((β_ (X 1) (X 0)).symm ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _)
      (((α_ (X 1) (X 0) (𝟙_ C)).symm ≪≫
      ((β_ (X 1) (X 0)) ⊗ᵢ Iso.refl _) ≪≫ α_ (X 0) (X 1) _).symm)
    apply heq_of_eq
    apply Iso.ext
    simp [tensorIso_hom, tensorIso_inv]
  | succ n ih =>
    intro i X
    refine Fin.cases ?_ (fun j => ?_) i
    · change HEq ((α_ (X 0) (X 1) _).symm ≪≫
        ((β_ (X 1) (X 0)).symm ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _)
        (((α_ (X 1) (X 0) _).symm ≪≫
        ((β_ (X 1) (X 0)) ⊗ᵢ Iso.refl _) ≪≫ α_ (X 0) (X 1) _).symm)
      apply heq_of_eq
      apply Iso.ext
      simp [tensorIso_hom, tensorIso_inv, coloredSwap, Fin.cases_succ]
    · simp only [coloredGeneratorInverse, coloredGenerator, coloredSwap, Fin.cases_zero,
        Fin.cases_succ]
      have h := ih j (fun k => X k.succ)
      have hp : coloredTensor (n + 2) (fun k => X k.succ) =
          coloredTensor (n + 2) (fun k => X (coloredSwap n j (coloredSwap n j k)).succ) := by
        congr 1
        funext k
        rw [coloredSwap_eq_swap]
        simp
      have ht := tensor_refl_heq_of_source_eq (A := X 0) _ _ hp h
      have hh {B D : C} (f : B ≅ D) :
          (Iso.refl (X 0) ⊗ᵢ f).symm = Iso.refl (X 0) ⊗ᵢ f.symm := by
        apply Iso.ext
        simp [tensorIso_hom, tensorIso_inv]
      simpa only [hh] using ht

end MTC.Braided.Cabling
end
