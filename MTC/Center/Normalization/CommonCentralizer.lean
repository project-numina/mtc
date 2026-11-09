module
public import MTC.Center.Normalization.MugerLabels
public import MTC.Center.ProductClosure

open MTC.Braided MTC.Center

/-! # Centralizer of the two canonical centre images

The common centralizer of positive and negative images is exactly the positive
image of the actual transparent objects. This is the first centralizer identity
in the manuscript's centre lemma, proved objectwise.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
namespace MTC.Center.Normalization
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- Two objects centralizing the same object have a tensor product that
centralizes it. -/
theorem doubleBraiding_tensor_left {X Y T : D}
    (hX : (β_ X T).hom ≫ (β_ T X).hom = 𝟙 _)
    (hY : (β_ Y T).hom ≫ (β_ T Y).hom = 𝟙 _) :
    (β_ (X ⊗ Y) T).hom ≫ (β_ T (X ⊗ Y)).hom = 𝟙 _ := by
  have hx : (β_ X T).hom = (β_ T X).inv := by
    apply (cancel_mono (β_ T X).hom).1
    simpa using hX
  have hy : (β_ Y T).hom = (β_ T Y).inv := by
    apply (cancel_mono (β_ T Y).hom).1
    simpa using hY
  simp [braiding_tensor_left_hom, braiding_tensor_right_hom, hx, hy, Category.assoc]

/-- The positive canonical centre images centralize precisely when their
underlying objects centralize. -/
theorem positiveImages_centralize_iff (X Y : D) :
    MTC.Center.Centralizes ((CategoryTheory.Center.ofBraided D).obj X)
      ((CategoryTheory.Center.ofBraided D).obj Y) ↔
      (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _ := by
  constructor
  · intro h
    exact congrArg CategoryTheory.Center.Hom.f h
  · intro h
    exact CategoryTheory.Center.ext _ _ h

/-- The common centralizer of the two canonical images consists exactly of
positive images of transparent objects, up to isomorphism. -/
theorem commonCanonicalCentralizer_iff (Z : CategoryTheory.Center D) :
    ((∀ X : D, MTC.Center.Centralizes Z ((CategoryTheory.Center.ofBraided D).obj X)) ∧
      (∀ X : D, MTC.Center.Centralizes Z ((MTC.Center.negative D).obj X))) ↔
    ∃ X : D, MTC.Center.Transparent X ∧
      Nonempty (Z ≅ (CategoryTheory.Center.ofBraided D).obj X) := by
  constructor
  · rintro ⟨hp, hn⟩
    let e := MTC.Center.positiveIsoOfCentralizesNegative Z hn
    refine ⟨Z.1, ?_, ⟨e⟩⟩
    intro X
    apply (positiveImages_centralize_iff _ _).mp
    exact MTC.Center.centralizes_of_iso_left e.symm (hp X)
  · rintro ⟨X, hX, ⟨e⟩⟩
    constructor
    · intro Y
      exact MTC.Center.centralizes_of_iso_left e ((positiveImages_centralize_iff _ _).mpr (hX Y))
    · intro Y
      exact MTC.Center.centralizes_of_iso_left e (MTC.Center.positive_negative_centralize X Y)

/-- Centralizing every product retract is equivalent to centralizing each
canonical image; the product-retract class is the generated centre subcategory. -/
theorem productRetractCentralizer_iff (Z : CategoryTheory.Center D) :
    (∀ P : CategoryTheory.Center D, MTC.Center.ProductRetract P → MTC.Center.Centralizes Z P) ↔
    ∃ X : D, MTC.Center.Transparent X ∧
      Nonempty (Z ≅ (CategoryTheory.Center.ofBraided D).obj X) := by
  rw [← commonCanonicalCentralizer_iff]
  constructor
  · intro h
    exact ⟨fun X ↦ h _ (MTC.Center.positive_productRetract X),
      fun X ↦ h _ (MTC.Center.negative_productRetract X)⟩
  · rintro ⟨hp, hn⟩ P ⟨X, Y, ⟨r⟩⟩
    apply MTC.Center.centralizes_symm
    apply MTC.Center.Braid.doubleBraiding_eq_one_of_retract r
    change MTC.Center.Centralizes
      (((CategoryTheory.Center.ofBraided D).obj X) ⊗ ((MTC.Center.negative D).obj Y)) Z
    exact doubleBraiding_tensor_left (MTC.Center.centralizes_symm (hp X))
      (MTC.Center.centralizes_symm (hn Y))

end MTC.Center.Normalization
end
