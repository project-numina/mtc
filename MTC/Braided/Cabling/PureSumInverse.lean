module
public import MTC.Braided.Cabling.PureSumColored
public import MTC.CategoryTheory.Monoidal.TensorIso

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

/-- The negative first crossing is the inverse of the positive crossing with exchanged inputs. -/
theorem firstCross_inverse (A B T : C) :
    (α_ A B T).symm ≪≫ ((β_ B A).symm ⊗ᵢ Iso.refl T) ≪≫ α_ B A T =
      ((α_ B A T).symm ≪≫ ((β_ B A) ⊗ᵢ Iso.refl T) ≪≫ α_ A B T).symm := by
  apply Iso.ext
  simp [tensorIso_hom, tensorIso_inv]


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
    exact heq_of_eq (firstCross_inverse (X 0) (X 1) (𝟙_ C))
  | succ n ih =>
    intro i X
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heq_of_eq (firstCross_inverse (X 0) (X 1)
        (coloredTensor (n + 1) (fun k => X k.succ.succ)))
    · simp only [coloredGeneratorInverse, coloredGenerator, coloredSwap, Fin.cases_zero,
        Fin.cases_succ]
      have h := ih j (fun k => X k.succ)
      have hp : coloredTensor (n + 2) (fun k => X k.succ) =
          coloredTensor (n + 2) (fun k => X (coloredSwap n j (coloredSwap n j k)).succ) := by
        congr 1
        funext k
        rw [coloredSwap_involutive]
      have ht := tensor_refl_heq_of_source_eq (A := X 0) _ _ hp h
      simpa only [MTC.tensorIso_symm, Iso.refl_symm] using ht

end MTC.Braided.Cabling
end
