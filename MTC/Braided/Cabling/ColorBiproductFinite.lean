module
public import MTC.Braided.Cabling.ColorBiproduct
public import MTC.Braided.Cabling.PureSumPreservation

/-! # Finite diagonal ranges from a concrete colored cabling realization

The actual colored-word realization by a fixed original-strand flattening is
an explicit hypothesis; this file does not assert that realization. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.Braided.Cabling
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C]
variable {I : Type} [Fintype I] [DecidableEq I] (V : I → C)

/-- A fixed cabled realization in a finite original-strand braid image gives
finite range for the corresponding actual pure-braid diagonal component. -/
theorem finite_pureColor_range_of_cabling (n r : ℕ) (f : Fin (n + 2) → I) (X : C)
    (e : coloredTensor (n + 2) (fun j => V (f j)) ≅ tensorPower X (r + 2))
    (hX : ObjectPropertyF X)
    (hcable : ∀ (w : List (Fin (n + 1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z : braidImage X r, coloredPureWordHom n w hw (fun j => V (f j)) =
        e.hom ≫ z.val.asIso.hom ≫ e.inv) :
    Set.Finite (Set.range fun h : pureBraidImage (⨁ V) n =>
      colorInclusion V (n + 2) f ≫ h.val.val.asIso.hom ≫ colorProjection V (n + 2) f) := by
  have h := finite_pureBlock_range_of_cabling
    (fun j => biproduct.ι V (f j)) (fun j => biproduct.π V (f j))
    (fun j => biproduct.ι_π_self V (f j)) e (hX r) hcable
  simpa only [← colorInclusion_eq_coloredBlockInclusion,
    ← colorProjection_eq_coloredBlockProjection] using h

end MTC.Braided.Cabling
end
