module
public import MTC.Braided.Cabling.BlockFinite
public import MTC.Braided.Cabling.ColorBiproduct
public import MTC.Braided.Cabling.PureSumPreservation

/-! # Finite pure block ranges imply finite braid images on sums -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Braided.Cabling
set_option backward.isDefEq.respectTransparency false
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C]
variable {I : Type} [Fintype I] [DecidableEq I] (V : I → C)

/-- For a finite sum, the full braid image is finite once each colored block
has finite diagonal range under the actual pure braid image. -/
theorem finite_braidImage_biproduct_of_finite_pure_block_ranges (n : ℕ)
    (hfinite : ∀ f : Fin (n+2) → I, Set.Finite (Set.range fun h : pureBraidImage (⨁ V) n =>
      colorInclusion V (n+2) f ≫ h.val.val.asIso.hom ≫ colorProjection V (n+2) f)) :
    Finite (braidImage (⨁ V) n) := by
  classical
  apply braidImage_finite_of_pureBraidImage_finite (⨁ V) n
  let A := pureBraidImage (⨁ V) n
  let g : A → Aut (tensorPower (⨁ V) (n+2)) := fun h => h.val.val
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply finite_type_of_finite_preserved_blocks
    (fun f : Fin (n+2) → I => coloredTensor (n+2) (fun j => V (f j)))
    (tensorPower (⨁ V) (n+2)) (colorInclusion V (n+2)) (colorProjection V (n+2))
    (colorProjection_inclusion_total V (n+2)) A g hg
  · intro h f
    have hp := pureBraidImage_preserves_coloredBlock n (fun j => V (f j)) (⨁ V)
      (fun j => biproduct.ι V (f j)) (fun j => biproduct.π V (f j))
      (fun j => biproduct.ι_π_self V (f j)) h
    simpa only [coloredBlockInclusion, coloredBlockProjection,
      ← colorInclusion_eq_coloredTensorMap, ← colorProjection_eq_coloredTensorMap] using hp
  · exact hfinite

end MTC.Braided.Cabling
end
