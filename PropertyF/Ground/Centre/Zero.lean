module
public import PropertyF.Ground.Centre.Linear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! The zero object of the Drinfeld centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped ZeroObject
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]

/-- Tensoring a zero object on the right remains a zero object. -/
theorem zeroTensorRight (U : C) : IsZero ((0 : C) ⊗ U) :=
  (tensorRight U).map_isZero (isZero_zero C)

/-- Tensoring a zero object on the left remains a zero object. -/
theorem zeroTensorLeft (U : C) : IsZero (U ⊗ (0 : C)) :=
  (tensorLeft U).map_isZero (isZero_zero C)

/-- The unique half-braiding on the zero object. -/
def centerZero : CategoryTheory.Center C :=
  ⟨0, { β := fun U => (zeroTensorRight U).iso (zeroTensorLeft U)
        monoidal := fun U U' => (zeroTensorRight (U ⊗ U')).eq_of_src _ _
        naturality := fun {U _U'} _f => (zeroTensorRight U).eq_of_src _ _ }⟩

omit [HasZeroObject C] in
/-- The forgetful functor detects zero objects. -/
theorem isZero_of_forget (Z : CategoryTheory.Center C) (h : IsZero Z.1) : IsZero Z := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply CategoryTheory.Center.ext
  exact h.eq_of_src _ _

/-- The constructed centre object over zero is a zero object. -/
theorem centerZero_isZero : IsZero (centerZero (C := C)) :=
  isZero_of_forget _ (isZero_zero C)

instance centerHasZeroObject : HasZeroObject (CategoryTheory.Center C) :=
  centerZero_isZero.hasZeroObject

end PropertyF.Ground.Centre
