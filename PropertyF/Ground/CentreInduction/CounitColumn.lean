module
public import PropertyF.Ground.CentreInduction.CrossingCoherence
public import PropertyF.Ground.CentreInduction.AdjunctionAssembly

/-! Matrix reductions for the induction adjunction. -/
section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- Composing a crossing with the unit-summand counit selects one matrix column. -/
theorem crossing_counit_matrix (X T : C.Obj) (i : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T ≫ (T ◁ (underlyingCounit C).app X) =
    (∑ a, crossingSummand C X T i (unitIndex C) a) ≫
      (T ◁ (unitSummandIso C X).hom) := by
  classical
  simpa only [underlyingCounit, unitSummandRetract, whiskerLeft_comp, Category.assoc] using
    congrArg (fun k => k ≫ (T ◁ (unitSummandIso C X).hom))
      (crossingCandidate_matrix C X T i (unitIndex C))


end PropertyF.Ground.CentreInduction

end
end

/-! The unit-column matrix of the induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

/-- Tensoring a simple by the chosen unit representative changes it by an isomorphism. -/
def simpleTensorUnitIso (j : Fin (rank C)) : simples C j ⊗ simples C (unitIndex C) ≅ simples C j :=
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  whiskerLeftIso (simples C j) e ≪≫ ρ_ (simples C j)

set_option backward.isDefEq.respectTransparency false in
/-- The counit crossing column has only diagonal simple summands. -/
theorem counit_column_finrank (i j : Fin (rank C)) :
    Module.finrank ℂ (simples C i ⟶ simples C j ⊗ simples C (unitIndex C)) = if i = j then 1 else 0 :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (simpleTensorUnitIso C j)).finrank_eq.trans
    (finrank_simples_hom C i j)

set_option backward.isDefEq.respectTransparency false in
/-- Off-diagonal counit crossing entries vanish. -/
theorem crossing_counit_offdiag (X : C.Obj) {i j : Fin (rank C)} (hne : i ≠ j) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ simples C j) ≫ crossingCandidate C X (simples C j) ≫
    (simples C j ◁ (underlyingCounit C).app X) = 0 := by
  classical
  have hdim : Module.finrank ℂ (simples C i ⟶ simples C j ⊗ simples C (unitIndex C)) = 0 := by
    rw [counit_column_finrank]; simp [hne]
  let : IsEmpty (crossingIndex C (simples C j) i (unitIndex C)) := by
    simp only [crossingIndex, hdim]
    infer_instance
  simpa only [Fintype.sum_empty, zero_comp] using crossing_counit_matrix C X (simples C j) i

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal entry is the canonical unit isomorphism block. -/
theorem crossing_counit_diagonal (X : C.Obj) (i : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ simples C i) ≫ crossingCandidate C X (simples C i) ≫
    (simples C i ◁ (underlyingCounit C).app X) =
      crossingBlock X (simples C i) (simples C i) (simples C (unitIndex C))
        (simpleTensorUnitIso C i).inv (simpleTensorUnitIso C i).hom ≫
          (simples C i ◁ (unitSummandIso C X).hom) := by
  classical
  have hdim : Module.finrank ℂ (simples C i ⟶ simples C i ⊗ simples C (unitIndex C)) = 1 := by
    rw [counit_column_finrank]; simp
  let a : crossingIndex C (simples C i) i (unitIndex C) := ⟨0, by rw [hdim]; decide⟩
  let : Subsingleton (crossingIndex C (simples C i) i (unitIndex C)) := by
    simp only [crossingIndex, hdim]
    infer_instance
  let : Unique (crossingIndex C (simples C i) i (unitIndex C)) :=
    ⟨⟨a⟩, fun b => Subsingleton.elim b a⟩
  have hh := crossing_counit_matrix C X (simples C i) i
  rw [Fintype.sum_unique, show (default : crossingIndex C (simples C i) i (unitIndex C)) = a
    from Subsingleton.elim _ _] at hh
  dsimp only [crossingSummand] at hh
  let : Simple (simples C i) := simples_simple C i
  let : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  rw [crossingBlock_of_simple_split X (simpleTensorUnitIso C i).symm _ _
    (crossingInclusion_projection a)] at hh
  exact hh

end PropertyF.Ground.CentreInduction
