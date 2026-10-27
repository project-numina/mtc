module
public import PropertyF.Ground.CentreCabling.VafaTwist

/-! Determinants of natural twists on simple-source multiplicity spaces. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u

/-- A natural endomorphism acts on maps out of a simple object by its scalar
component at that simple object. -/
theorem natural_postcomp_simple
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (i : Fin (rank C)) (X : C.Obj) :
    CategoryTheory.Linear.rightComp ℂ (simples C i) (α.app X) =
      (Calculus.groundSimpleScalar C i (End.of (α.app (simples C i)))) •
        (1 : (simples C i ⟶ X) →ₗ[ℂ] (simples C i ⟶ X)) := by
  ext f
  have hn := α.naturality f
  simp only [Functor.id_map] at hn
  change f ≫ α.app X = _
  calc
    _ = α.app (simples C i) ≫ f := hn
    _ = _ := by
      have hs := Calculus.groundSimpleScalar_smul_id C i (End.of (α.app (simples C i)))
      change _ = α.app (simples C i) at hs
      conv_lhs => rw [← hs]
      simp

/-- The determinant of a natural endomorphism on a simple-source Hom space
is the simple scalar raised to its actual vector-space dimension. -/
theorem determinant_natural_postcomp_simple
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (i : Fin (rank C)) (X : C.Obj) :
    LinearMap.det (CategoryTheory.Linear.rightComp ℂ (simples C i) (α.app X)) =
      (Calculus.groundSimpleScalar C i (End.of (α.app (simples C i)))) ^
        Module.finrank ℂ (simples C i ⟶ X) := by
  letI : FiniteDimensional ℂ (simples C i ⟶ X) := IsFusionCategory.hom_finite _ _
  rw [natural_postcomp_simple, LinearMap.det_smul]
  simp

/-- The fusion-rule multiplicity is the dimension of the actual lantern Hom
space, using the chosen representative of the dual simple. -/
theorem vafaMultiplicity_eq_finrank (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) :
    vafaMultiplicity C i = Module.finrank ℂ
      (simples C i ⟶ (simples C i ⊗ simples C (dualIndex C i)) ⊗ simples C i) := by
  let X := simples C i
  let Y := simples C (dualIndex C i)
  let e : (X ⊗ Y) ⊗ X ≅ X ⊗ (X ⊗ Y) := CategoryTheory.BraidedCategory.braiding _ _
  calc
    _ = Module.finrank ℂ (X ⟶ X ⊗ (X ⊗ Y)) := by
      unfold vafaMultiplicity
      rw [tensor_multiplicity]
      apply Finset.sum_congr rfl
      intro j hj
      change fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i =
        fusionCoeff C i (dualIndex C i) j * fusionCoeff C i j i
      rw [fusionCoeff_comm C j i]
    _ = _ := (CategoryTheory.Linear.homCongr ℂ (Iso.refl X) e).finrank_eq.symm

end PropertyF.Ground.CentreCabling
