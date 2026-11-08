module
public import MTC.Braided.Cabling.Naturality

/-! Actual categorical braidings of independently colored tensor strands. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A right-associated tensor product of independently chosen strands. -/
def coloredTensor : ∀ n : ℕ, (Fin n → C) → C
  | 0, _ => 𝟙_ C
  | n + 1, X => X 0 ⊗ coloredTensor n (fun i => X i.succ)

/-- Swap adjacent positions, recursively respecting the tensor association. -/
def coloredSwap : (n : ℕ) → Fin (n + 1) → Fin (n + 2) → Fin (n + 2)
  | 0, _ => Fin.cases 1 (Fin.cases 0 (fun i => nomatch i))
  | n + 1, i => Fin.cases
      (Fin.cases 1 (Fin.cases 0 (fun j => j.succ.succ)))
      (fun j => Fin.cases 0 (fun k => (coloredSwap n j k).succ)) i

/-- The recursive swap is exactly the adjacent permutation used by braid words. -/
theorem coloredSwap_eq_swap : ∀ (n : ℕ) (i : Fin (n + 1)),
    coloredSwap n i = Equiv.swap i.castSucc i.succ := by
  intro n
  induction n with
  | zero =>
    intro i
    fin_cases i
    funext j
    fin_cases j <;> decide
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · funext j
      refine Fin.cases ?_ (fun l => ?_) j
      · simp [coloredSwap, Equiv.swap_apply_def]
      · refine Fin.cases ?_ (fun t => ?_) l
        · change (0 : Fin (n + 3)) = 0
          rfl
        · simp [coloredSwap, Equiv.swap_apply_def]
          intro h
          have hh := congrArg Fin.val h
          simp at hh
    · funext j
      refine Fin.cases ?_ (fun l => ?_) j
      · simp only [coloredSwap, Equiv.swap_apply_def, Fin.cases_zero]
        split_ifs with h h <;> simp_all
      · simp [coloredSwap, ih, Equiv.swap_apply_def] <;> split_ifs <;> simp_all

/-- The actual adjacent braiding between differently colored strands. -/
def coloredGenerator : ∀ (n : ℕ) (i : Fin (n + 1)) (X : Fin (n + 2) → C),
    coloredTensor (n + 2) X ≅ coloredTensor (n + 2) (fun j => X (coloredSwap n i j))
  | 0, _, X =>
      (α_ (X 0) (X 1) (𝟙_ C)).symm ≪≫
        ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl (𝟙_ C)) ≪≫
        (α_ (X 1) (X 0) (𝟙_ C))
  | n + 1, i, X => Fin.cases
      ((α_ (X 0) (X 1) (coloredTensor (n + 1) (fun k => X k.succ.succ))).symm ≪≫
        ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl _) ≪≫
        (α_ (X 1) (X 0) (coloredTensor (n + 1) (fun k => X k.succ.succ))))
      (fun j => Iso.refl (X 0) ⊗ᵢ coloredGenerator n j (fun k => X k.succ)) i

/-- Tensor independent maps on each colored strand. -/
def coloredTensorMap : ∀ (n : ℕ) {X Y : Fin n → C},
    (∀ i, X i ⟶ Y i) → (coloredTensor n X ⟶ coloredTensor n Y)
  | 0, _, _, _ => 𝟙 _
  | n + 1, _, _, f => f 0 ⊗ₘ coloredTensorMap n (fun i => f i.succ)

/-- Naturality of a crossing of two different strands with a spectator tail. -/
theorem colored_first_map {X Y X' Y' A B : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : A ⟶ B) :
    ((α_ X Y A).symm ≪≫ ((β_ X Y) ⊗ᵢ Iso.refl A) ≪≫ α_ Y X A).hom ≫
        (g ⊗ₘ (f ⊗ₘ h)) =
      (f ⊗ₘ (g ⊗ₘ h)) ≫
        ((α_ X' Y' B).symm ≪≫ ((β_ X' Y') ⊗ᵢ Iso.refl B) ≪≫ α_ Y' X' B).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← associator_naturality, associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    braiding_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- A colored adjacent crossing is natural in the independent strand maps. -/
theorem coloredGenerator_natural : ∀ (n : ℕ) (i : Fin (n + 1))
    {X Y : Fin (n + 2) → C} (f : ∀ j, X j ⟶ Y j),
    (coloredGenerator n i X).hom ≫
      coloredTensorMap (n + 2) (fun j => f (coloredSwap n i j)) =
    coloredTensorMap (n + 2) f ≫ (coloredGenerator n i Y).hom := by
  intro n
  induction n with
  | zero =>
    intro i X Y f
    fin_cases i
    change ((α_ (X 0) (X 1) (𝟙_ C)).symm ≪≫ ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _).hom ≫
      (f 1 ⊗ₘ (f 0 ⊗ₘ 𝟙 _)) = (f 0 ⊗ₘ (f 1 ⊗ₘ 𝟙 _)) ≫
      ((α_ (Y 0) (Y 1) (𝟙_ C)).symm ≪≫ ((β_ (Y 0) (Y 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (Y 1) (Y 0) _).hom
    exact colored_first_map (f 0) (f 1) (𝟙 _)
  | succ n ih =>
    intro i X Y f
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((α_ (X 0) (X 1) _).symm ≪≫ ((β_ (X 0) (X 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (X 1) (X 0) _).hom ≫
        (f 1 ⊗ₘ (f 0 ⊗ₘ coloredTensorMap (n + 1) (fun k => f k.succ.succ))) =
        (f 0 ⊗ₘ (f 1 ⊗ₘ coloredTensorMap (n + 1) (fun k => f k.succ.succ))) ≫
        ((α_ (Y 0) (Y 1) _).symm ≪≫ ((β_ (Y 0) (Y 1)) ⊗ᵢ Iso.refl _) ≪≫ α_ (Y 1) (Y 0) _).hom
      exact colored_first_map (f 0) (f 1) _
    · change (𝟙 (X 0) ⊗ₘ (coloredGenerator n j (fun k => X k.succ)).hom) ≫
        (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f (coloredSwap n j k).succ)) =
        (f 0 ⊗ₘ coloredTensorMap (n + 2) (fun k => f k.succ)) ≫
        (𝟙 (Y 0) ⊗ₘ (coloredGenerator n j (fun k => Y k.succ)).hom)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [ih j (fun k => f k.succ)]

end MTC.Braided.Cabling
end
