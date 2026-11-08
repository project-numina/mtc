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

end MTC.Braided.Cabling
end
