module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Algebra.Group.Subgroup.Map

/-! The group-theoretic part of preservation of braid images under functors. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal
namespace PropertyF


universe v u w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type z} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]

/-- The canonical comparison between a tensor power of the image and the
image of a tensor power for a strong monoidal functor. -/
def tensorPowerFunctorIso (F : C ⥤ D) [F.Monoidal] (X : C) : ∀ n,
    tensorPower (F.obj X) n ≅ F.obj (tensorPower X n)
  | 0 => εIso F
  | n + 1 => (Iso.refl (F.obj X) ⊗ᵢ tensorPowerFunctorIso F X n) ≪≫
      μIso F X (tensorPower X n)


end PropertyF
