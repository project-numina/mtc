module
public import PropertyF.Ground.Cabling.Naturality
public import Mathlib.CategoryTheory.Monoidal.Preadditive
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [MonoidalPreadditive C]

omit [BraidedCategory C] in
/-- Tensoring a zero object on the right remains zero. -/
theorem zero_tensor_isZero {X : C} (h : IsZero X) (Y : C) : IsZero (X ⊗ Y) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← id_tensorHom_id, (IsZero.iff_id_eq_zero X).mp h]
  simp

/-- The zero object has property F in any braided preadditive monoidal category. -/
theorem objectPropertyF_of_isZero {X : C} (h : IsZero X) : ObjectPropertyF X := by
  intro n
  have hp : IsZero (tensorPower X (n + 2)) := zero_tensor_isZero h _
  let _ : Subsingleton (Aut (tensorPower X (n + 2))) := ⟨fun a b => by
    apply Aut.ext
    apply Iso.ext
    exact hp.eq_of_src _ _⟩
  have : Subsingleton (braidImage X n) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Finite.of_injective (fun _ : braidImage X n => PUnit.unit) (fun a b _ => Subsingleton.elim _ _)
end PropertyF
