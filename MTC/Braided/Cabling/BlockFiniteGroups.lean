module
public import MTC.Braided.Cabling.BlockFiniteSum

/-! # Finite colored groups imply property F of finite sums -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.Braided.Cabling
set_option backward.isDefEq.respectTransparency false
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C]
variable {I : Type} [Fintype I] [DecidableEq I] (V : I → C)

/-- If each colored pure-word action lies in an actual finite subgroup, the
finite biproduct has property F. The subgroup input is an explicit cabling
interface, and this result does not assert it exists for arbitrary V. -/
theorem objectPropertyF_biproduct_of_finite_colored_groups
    (H : ∀ (n : ℕ) (f : Fin (n+2) → I),
      Subgroup (Aut (coloredTensor (n+2) (fun j => V (f j)))))
    (hH : ∀ n f, Finite (H n f))
    (hcable : ∀ n f (w : List (Fin (n+1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z : H n f, z.val.asIso.hom =
        coloredPureWordHom n w hw (fun j => V (f j))) :
    ObjectPropertyF (⨁ V) := by
  intro n
  apply finite_braidImage_biproduct_of_finite_pure_block_ranges V n
  intro f
  have hr := finite_pureBlock_range_of_colored_group n (fun j => V (f j)) (⨁ V)
    (fun j => biproduct.ι V (f j)) (fun j => biproduct.π V (f j))
    (fun j => biproduct.ι_π_self V (f j)) (H n f) (hH n f) (hcable n f)
  simpa only [← colorInclusion_eq_coloredBlockInclusion,
    ← colorProjection_eq_coloredBlockProjection] using hr

end MTC.Braided.Cabling
end
