module
public import PropertyF.Ground.Cabling.Naturality
public import Mathlib.CategoryTheory.Monoidal.Preadditive
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [MonoidalPreadditive C]

/-- The zero object has property F in any braided preadditive monoidal category. -/
theorem objectPropertyF_of_isZero {X : C} (h : IsZero X) : ObjectPropertyF X := by
  intro n
  have hp : IsZero (tensorPower X (n + 2)) := Functor.map_isZero (tensorRight _) h
  let _ : Subsingleton (Aut (tensorPower X (n + 2))) := ⟨fun a b => by
    apply Aut.ext
    apply Iso.ext
    exact hp.eq_of_src _ _⟩
  exact Finite.of_injective (Subtype.val : braidImage X n → Aut (tensorPower X (n + 2)))
    Subtype.val_injective
end PropertyF
