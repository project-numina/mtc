module
public import PropertyF.Ground.Dimensions.Norm
public import PropertyF.Ground.Dimensions.Trace
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

/-- Intrinsic squared norms are invariant under simple-object isomorphism,
without assuming a pivotal or spherical structure. -/
theorem target_squaredNorm_iso (C : Ground.BraidedFusionCategory.{v,u})
    {X Y : C.Obj} [Simple X] [Simple Y] (e : X ≅ Y) :
    Ground.squaredNorm C X = Ground.squaredNorm C Y := by
  let j := Ground.doubleDualIso C X
  let k : Y ≅ (Yᘁ)ᘁ := e.symm ≪≫ j ≪≫ rightDualIsoMap (rightDualIsoMap e)
  have hnat : e.hom ≫ k.hom = j.hom ≫ (e.homᘁ)ᘁ := by
    simp [k, rightDualIsoMap]
  have h := quantumTraces_iso j k e hnat
  rw [target_squaredNorm_choice_independent C X j,
      target_squaredNorm_choice_independent C Y k, h.1, h.2]

/-- Any complete, pairwise nonisomorphic finite list of simple objects can
be used to compute the intrinsic global dimension. -/
theorem target_globalDimension_independent_simples (C : Ground.BraidedFusionCategory.{v,u})
    {n : ℕ} (T : Fin n → C.Obj) (hs : ∀ i, Simple (T i))
    (hinj : ∀ i j, Nonempty (T i ≅ T j) → i = j)
    (hcomplete : ∀ X : C.Obj, Simple X → ∃ i, Nonempty (X ≅ T i)) :
    Ground.globalDimension C = ∑ i, Ground.squaredNorm C (T i) := by
  classical
  let f : Fin (Ground.rank C) → Fin n := fun i =>
    Classical.choose (hcomplete (Ground.simples C i) (Ground.simples_simple C i))
  have hf (i : Fin (Ground.rank C)) : Nonempty (Ground.simples C i ≅ T (f i)) :=
    Classical.choose_spec (hcomplete (Ground.simples C i) (Ground.simples_simple C i))
  have finj : Function.Injective f := by
    intro i j hij
    obtain ⟨ei⟩ := hf i
    obtain ⟨ej⟩ := hf j
    apply Ground.simples_injective C i j
    exact ⟨ei ≪≫ eqToIso (congrArg T hij) ≪≫ ej.symm⟩
  have fsurj : Function.Surjective f := by
    intro i
    let : Simple (T i) := hs i
    obtain ⟨j, ⟨e⟩⟩ := Ground.exists_simple_iso C (T i)
    refine ⟨j, ?_⟩
    apply (hinj _ _ ?_).symm
    obtain ⟨e'⟩ := hf j
    exact ⟨e ≪≫ e'⟩
  let eqv : Fin (Ground.rank C) ≃ Fin n := Equiv.ofBijective f ⟨finj, fsurj⟩
  unfold Ground.globalDimension
  apply Fintype.sum_equiv eqv
  intro i
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  let : Simple (T (f i)) := hs (f i)
  obtain ⟨e⟩ := hf i
  exact target_squaredNorm_iso C e

/-- In a spherical braided fusion category, the target norm is invariant under
isomorphism of simple objects. -/
theorem target_squaredNorm_iso_of_spherical (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    {X Y : C.Obj} [Simple X] [Simple Y] (e : X ≅ Y) :
    Ground.squaredNorm C X = Ground.squaredNorm C Y := by
  rw [target_squaredNorm_eq_dimension_sq C p hp X, target_squaredNorm_eq_dimension_sq C p hp Y]
  have h : rightQuantumTrace (p.iso X) = rightQuantumTrace (p.iso Y) := by
    rw [← rightTrace_id, ← rightTrace_id]
    exact p.rightTrace_id_iso e
  rw [h]

end PropertyF.Ground.Dimensions
