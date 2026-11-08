module
public import MTC.Center.Normalization.SymmetricRising
public import MTC.Center.Normalization.BinomialArithmetic
public import MTC.Center.Normalization.IntegerDimensions

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Integer dimensions in symmetric fusion categories -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (hsym : ∀ X Y : C.Obj, MTC.Modular.doubleBraiding X Y = 𝟙 _)

/-- Every simple object of a symmetric fusion category has integer dimension
for the canonical symmetric pivotal structure. -/
theorem canonicalSymmetricPivotal_simple_integer (X : C.Obj) [Simple X] :
    ∃ m : ℤ, pivotalDimension C (canonicalSymmetricPivotal hsym) X = (m : ℂ) := by
  apply integer_of_integral_falling_rising
  · exact pivotalDimension_isIntegral C (canonicalSymmetricPivotal hsym) X
  · exact canonicalSymmetricPivotal_falling_binomial_isIntegral C hsym X
  · exact canonicalSymmetricPivotal_rising_binomial_isIntegral C hsym X

/-- Every object of a symmetric fusion category has integer dimension for the
canonical symmetric pivotal structure. -/
theorem canonicalSymmetricPivotal_integer (X : C.Obj) :
    ∃ m : ℤ, pivotalDimension C (canonicalSymmetricPivotal hsym) X = (m : ℂ) := by
  apply pivotalDimension_integer_of_simple_integers (canonicalSymmetricPivotal hsym) _ X
  intro i
  let : Simple (simples C i) := simples_simple C i
  exact canonicalSymmetricPivotal_simple_integer C hsym (simples C i)

/-- Every object of the actual Müger fusion category has integer dimension for
its canonical spherical pivotal structure. -/
theorem mugerCanonicalPivotal_integer (X : MugerCategory C) :
    ∃ m : ℤ, pivotalDimension (bundledMuger C) (mugerCanonicalPivotal C) X = (m : ℂ) :=
  canonicalSymmetricPivotal_integer (bundledMuger C) (mugerBraiding_symmetric C) X

end MTC.Center.Normalization
end
