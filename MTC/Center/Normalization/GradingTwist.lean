module
public import MTC.Center.Normalization.UniversalGrading
public import MTC.Center.Normalization.PivotalTwist

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Twisting pivotal structures by fusion-degree characters -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable {C : BraidedFusionCategory.{v,u}}

/-- Character value on a simple object's universal fusion degree. -/
def characterScalar (χ : Multiplicative (FusionDegreeGroup C) →* ℂˣ)
    (i : Fin (rank C)) : ℂ := χ (Multiplicative.ofAdd (fusionDegree C i))

theorem characterScalar_ne_zero (χ : Multiplicative (FusionDegreeGroup C) →* ℂˣ)
    (i : Fin (rank C)) : characterScalar χ i ≠ 0 := Units.ne_zero _

theorem characterScalar_unit (χ : Multiplicative (FusionDegreeGroup C) →* ℂˣ) :
    characterScalar χ (unitIndex C) = 1 := by
  simp [characterScalar, fusionDegree_unit]

theorem characterScalar_tensor (χ : Multiplicative (FusionDegreeGroup C) →* ℂˣ)
    (i j k : Fin (rank C)) (h : 0 < fusionCoeff C i j k) :
    characterScalar χ k = characterScalar χ i * characterScalar χ j := by
  simp [characterScalar, fusionDegree_tensor C h]

/-- A character of the presented fusion-degree group twists an actual pivotal
structure. -/
def pivotalTwistOfDegreeCharacter (p : PivotalStructure (C := C.Obj))
    (χ : Multiplicative (FusionDegreeGroup C) →* ℂˣ) : PivotalStructure (C := C.Obj) :=
  scalarPivotalTwist p (characterScalar χ) (characterScalar_ne_zero χ)
    (characterScalar_unit χ) (characterScalar_tensor χ)

/-- Twisting by a fusion-degree character multiplies the pivotal dimension of
each simple by the character value on its degree. -/
theorem pivotalTwistOfDegreeCharacter_dimension (p : PivotalStructure (C := C.Obj))
    (χ : Multiplicative (FusionDegreeGroup C) →* ℂˣ) (i : Fin (rank C)) :
    pivotalDimension C (pivotalTwistOfDegreeCharacter p χ) (simples C i) =
      characterScalar χ i * pivotalDimension C p (simples C i) :=
  scalarPivotalTwist_dimension p _ _ _ _ i

end MTC.Center.Normalization
end
