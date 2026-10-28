module
public import PropertyF.Ground.Target
public import PropertyF.Ground.Fusion.Multiplicity
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The unit scalar map is invertible for every genuine complex fusion category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Schur's lemma identifies endomorphisms of the simple tensor unit with ℂ. -/
theorem unit_algebraMap_bijective : Function.Bijective (algebraMap ℂ (End (𝟙_ C.Obj))) := by
  let : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := IsFusionCategory.hom_finite _ _
  exact simple_algebraMap_bijective _

/-- The canonical scalar identification is an algebra equivalence. -/
def unitScalarEquiv : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ :=
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  letI : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := IsFusionCategory.hom_finite _ _
  simpleEndScalar _

/-- The scalar inverse used by the ground target really inverts the canonical
algebra map; no fallback value is reachable. -/
theorem unitScalar_algebraMap (z : ℂ) : unitScalar C (algebraMap ℂ (End (𝟙_ C.Obj)) z) = z :=
  (unit_algebraMap_bijective C).1 (Function.invFun_eq ⟨z, rfl⟩)

theorem algebraMap_unitScalar (f : End (𝟙_ C.Obj)) :
    algebraMap ℂ (End (𝟙_ C.Obj)) (unitScalar C f) = f :=
  Function.invFun_eq ((unit_algebraMap_bijective C).2 f)

theorem unitScalar_eq_equiv (f : End (𝟙_ C.Obj)) :
    unitScalar C f = unitScalarEquiv C f := by
  apply (unit_algebraMap_bijective C).1
  rw [algebraMap_unitScalar]
  exact (unitScalarEquiv C).symm_apply_apply f |>.symm

end PropertyF.Ground
