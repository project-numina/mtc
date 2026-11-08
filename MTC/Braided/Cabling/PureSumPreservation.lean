module
public import MTC.Braided.Cabling.PureSum
public import MTC.Braided.Cabling.PureSumColored

/-! Actual pure braid images preserve each colored retract block. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Every element of the actual pure braid image preserves a colored block. -/
theorem pureBraidImage_preserves_coloredBlock (n : ℕ)
    (X : Fin (n + 2) → C) (Y : C) (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) (h : pureBraidImage Y n) :
    let ι := coloredBlockInclusion (n + 2) X Y f
    let π := coloredBlockProjection (n + 2) X Y g
    let b := h.val.val.asIso.hom
    ι ≫ b = (ι ≫ b ≫ π) ≫ ι := by
  obtain ⟨w, hw, he⟩ := h.property
  obtain ⟨l, hl⟩ := Quot.exists_rep w
  change FreeGroup.mk l = w at hl
  subst w
  change strandPermutation n (FreeGroup.mk l) = 1 at hw
  rw [← he]
  exact pureWord_preserves_coloredBlock n l hw X Y f g hf

end MTC.Braided.Cabling
end
