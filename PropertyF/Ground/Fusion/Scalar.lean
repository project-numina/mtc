module
public import PropertyF.Ground.Fusion.Simples

/-! Scalar endomorphisms of the tensor unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace PropertyF.Ground
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Schur's lemma identifies endomorphisms of the unit with the ground field. -/
theorem unit_algebraMap_bijective : Function.Bijective
    (algebraMap ℂ (End (𝟙_ C.Obj))) := by
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  letI : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := IsFusionCategory.hom_finite _ _
  constructor
  · exact RingHom.injective _
  · intro f
    obtain ⟨z, hz⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f.asHom
    refine ⟨z, ?_⟩
    apply End.ext
    simpa [Algebra.algebraMap_eq_smul_one] using hz

theorem unitScalar_algebraMap (z : ℂ) :
    unitScalar C (algebraMap ℂ (End (𝟙_ C.Obj)) z) = z :=
  Function.leftInverse_invFun (unit_algebraMap_bijective C).1 z

theorem algebraMap_unitScalar (f : End (𝟙_ C.Obj)) :
    algebraMap ℂ (End (𝟙_ C.Obj)) (unitScalar C f) = f :=
  Function.rightInverse_invFun (unit_algebraMap_bijective C).2 f

end PropertyF.Ground
