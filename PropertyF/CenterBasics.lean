module
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.Tactic

/-!
# Centralizers in the monoidal centre

Positive and negative half-braidings and transparency.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Underlying double-braiding condition for centralizing the positive canonical
image. These are actual half-braidings in Mathlib's centre. -/
def CentralizesPositive (Y : CategoryTheory.Center C) : Prop :=
  ∀ X : C, (Y.2.β X).hom ≫ (β_ X Y.1).hom = 𝟙 _

/-- The negative canonical image has half-braiding `c(-,X)⁻¹`. -/
def CentralizesNegative (Y : CategoryTheory.Center C) : Prop :=
  ∀ X : C, (Y.2.β X).hom ≫ (β_ Y.1 X).inv = 𝟙 _

def IsPositive (Y : CategoryTheory.Center C) : Prop := ∀ X : C, Y.2.β X = β_ Y.1 X

def IsNegative (Y : CategoryTheory.Center C) : Prop := ∀ X : C, Y.2.β X = (β_ X Y.1).symm

/-- An object is transparent precisely when its double braiding with every
object is the identity. -/
def Transparent (V : C) : Prop := ∀ X : C,
  (β_ V X).hom ≫ (β_ X V).hom = 𝟙 _

/-- The mutual-centralizer calculation in Lemma 4.1, positive side. -/
theorem centralizesPositive_iff (Y : CategoryTheory.Center C) :
    CentralizesPositive Y ↔ IsNegative Y := by
  constructor
  · intro h X
    apply Iso.ext
    apply (cancel_mono (β_ X Y.1).hom).mp
    simpa using h X
  · intro h X
    rw [h X]
    simp

/-- The same calculation for the negative canonical image. -/
theorem centralizesNegative_iff (Y : CategoryTheory.Center C) :
    CentralizesNegative Y ↔ IsPositive Y := by
  constructor
  · intro h X
    apply Iso.ext
    apply (cancel_mono (β_ Y.1 X).inv).mp
    simpa using h X
  · intro h X
    rw [h X]
    simp

end PropertyF
