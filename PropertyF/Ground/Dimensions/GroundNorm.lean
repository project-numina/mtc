module
public import PropertyF.Ground.Dimensions.Norm
public import PropertyF.Ground.Dimensions.Pivotal
public import PropertyF.Ground.Fusion.Scalar

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

universe v u

/-- The target's scalar extraction is an algebra equivalence, as a
consequence of the fusion-category axioms. -/
def groundUnitScalarEquiv (C : Ground.BraidedFusionCategory.{v,u}) :
    End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ :=
  (AlgEquiv.ofBijective (Algebra.ofId ℂ (End (𝟙_ C.Obj)))
    (Ground.unit_algebraMap_bijective C)).symm

theorem groundUnitScalarEquiv_apply (C : Ground.BraidedFusionCategory.{v,u})
    (a : End (𝟙_ C.Obj)) : groundUnitScalarEquiv C a = Ground.unitScalar C a := by
  apply (Ground.unit_algebraMap_bijective C).1
  rw [Ground.algebraMap_unitScalar]
  exact (groundUnitScalarEquiv C).symm_apply_apply a

/-- For every simple object of a genuine braided fusion category, the
intrinsic squared norm in the target is independent of the chosen double-dual
isomorphism. -/
theorem target_squaredNorm_choice_independent (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] (j : X ≅ ((Xᘁ)ᘁ)) :
    Ground.squaredNorm C X =
      Ground.unitScalar C (rightQuantumTrace j) * Ground.unitScalar C (leftQuantumTrace j) := by
  let : FiniteDimensional ℂ (X ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  unfold Ground.squaredNorm
  simp only [← groundUnitScalarEquiv_apply]
  exact squaredNorm_independent (groundUnitScalarEquiv C) (Ground.doubleDualIso C X) j

/-- With any spherical structure the target norm of a simple object is its
categorical dimension squared. -/
theorem target_squaredNorm_eq_dimension_sq (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (X : C.Obj) [Simple X] :
    Ground.squaredNorm C X =
      (Ground.unitScalar C (rightQuantumTrace (p.iso X))) ^ 2 := by
  rw [target_squaredNorm_choice_independent C X (p.iso X),
    ← spherical_quantumTraces_eq p hp X, pow_two]

/-- The target's intrinsic global dimension is the sum of squared spherical
simple dimensions, for any spherical structure. -/
theorem target_globalDimension_eq_sum_squares (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) :
    Ground.globalDimension C = ∑ i : Fin (Ground.rank C),
      (Ground.unitScalar C (rightQuantumTrace (p.iso (Ground.simples C i)))) ^ 2 := by
  unfold Ground.globalDimension
  apply Finset.sum_congr rfl
  intro i _
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact target_squaredNorm_eq_dimension_sq C p hp (Ground.simples C i)

end PropertyF.Ground.Dimensions
