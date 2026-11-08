module
public import MTC.Braided.Cabling.BlockFinite

/-! # From finite blockwise pure-word actions to finite braid images -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u w

/-- A braid image is finite if its pure words preserve a finite family of
blocks resolving the identity and have finite diagonal range on each block. -/
theorem finite_braidImage_of_finite_pure_block_ranges
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
    {I : Type w} [Fintype I] (Y : C) (n : ℕ)
    (B : I → C) (ι : ∀ i, B i ⟶ tensorPower Y (n+2))
    (π : ∀ i, tensorPower Y (n+2) ⟶ B i)
    (hresolution : (∑ i, π i ≫ ι i) = 𝟙 (tensorPower Y (n+2)))
    (hpreserve : ∀ (w : (strandPermutation n).ker) i,
      ι i ≫ ((braidWordAction Y n w.val).val).asIso.hom =
        (ι i ≫ ((braidWordAction Y n w.val).val).asIso.hom ≫ π i) ≫ ι i)
    (hfinite : ∀ i, Set.Finite (Set.range fun w : (strandPermutation n).ker =>
      ι i ≫ ((braidWordAction Y n w.val).val).asIso.hom ≫ π i)) :
    Finite (braidImage Y n) := by
  classical
  apply braidImage_finite_of_pureBraidImage_finite Y n
  let A := pureBraidImage Y n
  let g : A → Aut (tensorPower Y (n+2)) := fun h => h.val.val
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have hrep (h : A) : ∃ w : (strandPermutation n).ker,
      (braidWordAction Y n w.val).val = g h := by
    obtain ⟨w, hw, he⟩ := h.property
    exact ⟨⟨w, hw⟩, congrArg Subtype.val he⟩
  apply finite_type_of_finite_preserved_blocks B (tensorPower Y (n+2)) ι π hresolution A g hg
  · intro h i
    obtain ⟨w, hw⟩ := hrep h
    rw [← hw]
    exact hpreserve w i
  · intro i
    apply (hfinite i).subset
    rintro _ ⟨h, rfl⟩
    obtain ⟨w, hw⟩ := hrep h
    refine ⟨w, ?_⟩
    change ι i ≫ ((braidWordAction Y n w.val).val).asIso.hom ≫ π i =
      ι i ≫ (g h).asIso.hom ≫ π i
    rw [hw]

end MTC.Braided.Cabling
end
