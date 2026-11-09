module
public import Mathlib.CategoryTheory.Monoidal.Category

/-! Basic identities for tensor products of isomorphisms. -/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensoring identity isomorphisms gives the identity isomorphism. -/
theorem tensorIso_refl (X Y : C) :
    (Iso.refl X ⊗ᵢ Iso.refl Y) = Iso.refl (X ⊗ Y) := Iso.ext (by simp)

/-- Taking inverses commutes with tensoring isomorphisms. -/
theorem tensorIso_symm {A B D E : C} (e : A ≅ B) (f : D ≅ E) :
    (e ⊗ᵢ f).symm = e.symm ⊗ᵢ f.symm := by
  apply Iso.ext
  rfl

end MTC
