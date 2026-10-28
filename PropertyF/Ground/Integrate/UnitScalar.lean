module
public import PropertyF.Ground.Target
public import PropertyF.Ground.Fusion.Multiplicity
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Scalars on the tensor unit

Schur's lemma identifies the endomorphisms of the tensor unit with complex
scalars. The inverse agrees with the scalar map in the target statement. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Schur's lemma identifies endomorphisms of the simple tensor unit with ℂ. -/
theorem unit_algebraMap_bijective : Function.Bijective (algebraMap ℂ (End (𝟙_ C.Obj))) :=
  let : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := IsFusionCategory.hom_finite _ _
  simple_algebraMap_bijective _

/-- The canonical scalar identification is an algebra equivalence. -/
def unitScalarEquiv : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ :=
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  letI : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := IsFusionCategory.hom_finite _ _
  simpleEndScalar _

/-- The scalar inverse used by the ground target really inverts the canonical
algebra map; no fallback value is reachable. -/
theorem unitScalar_algebraMap (z : ℂ) : unitScalar C (algebraMap ℂ (End (𝟙_ C.Obj)) z) = z :=
  (unit_algebraMap_bijective C).1 (Function.invFun_eq ⟨z, rfl⟩)

/-- The canonical scalar map also inverts the algebra map on endomorphisms. -/
theorem algebraMap_unitScalar (f : End (𝟙_ C.Obj)) :
    algebraMap ℂ (End (𝟙_ C.Obj)) (unitScalar C f) = f :=
  Function.invFun_eq ((unit_algebraMap_bijective C).2 f)

/-- The target's scalar map agrees with the canonical algebra equivalence. -/
theorem unitScalar_eq_equiv (f : End (𝟙_ C.Obj)) :
    unitScalar C f = unitScalarEquiv C f :=
  (congrArg (unitScalar C) ((unitScalarEquiv C).symm_apply_apply f).symm).trans
    (unitScalar_algebraMap C _)

end PropertyF.Ground
