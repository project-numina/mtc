module
public import PropertyF.Ground.Integrate.UnitScalar
public import PropertyF.Ground.Dimensions.Norm

/-! Connect the ground target's intrinsic norm to an arbitrary choice of
simple double-dual isomorphism and unit-scalar equivalence. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- The target norm is independent of both choices used in the conventional
trace definition, for a fixed simple object. -/
theorem squaredNorm_eq_of_choices (X : C.Obj) [Simple X]
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (j : X ≅ ((Xᘁ)ᘁ)) :
    squaredNorm C X = scalar (rightQuantumTrace j) * scalar (leftQuantumTrace j) := by
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  unfold squaredNorm
  rw [unitScalar_eq_equiv, unitScalar_eq_equiv]
  rw [← Dimensions.unitScalar_unique (unitScalarEquiv C) scalar (rightQuantumTrace j),
      ← Dimensions.unitScalar_unique (unitScalarEquiv C) scalar (leftQuantumTrace j)]
  exact Dimensions.squaredNorm_independent (unitScalarEquiv C) (doubleDualIso C X) j

end PropertyF.Ground
