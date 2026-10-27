module
public import PropertyF.Ground.CentreInduction.CandidateAssembly

/-! Matrix reductions for the induction adjunction. -/
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
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T ≫ (T ◁ (underlyingCounit C).app X) =
    (∑ a, crossingBlock C X T (simples C i) (simples C (unitIndex C))
      (crossingInclusion C T i (unitIndex C) a) (crossingProjection C T i (unitIndex C) a)) ≫
      (T ◁ (unitSummandIso C X).hom) := by
  classical
  have h := crossingCandidate_matrix C X T i (unitIndex C)
  have hh := congrArg (fun k => k ≫ (T ◁ (unitSummandIso C X).hom)) h
  simpa only [underlyingCounit, unitSummandRetract, whiskerLeft_comp, Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
/-- A split crossing block is independent of the chosen splitting of a simple. -/
theorem crossingBlock_of_simple_split (X T R S : C.Obj) [Simple R]
    (e : R ≅ T ⊗ S) (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) (h : g ≫ f = 𝟙 R) :
    crossingBlock C X T R S g f = crossingBlock C X T R S e.hom e.inv := by
  letI : FiniteDimensional ℂ (R ⟶ R) := IsFusionCategory.hom_finite _ _
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (g ≫ e.inv)
  obtain ⟨d, hd⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (e.hom ≫ f)
  have hg : g = c • e.hom := by
    have hh := congrArg (fun k => k ≫ e.hom) hc
    simpa [Category.assoc] using hh.symm
  have hf : f = d • e.inv := by
    have hh := congrArg (fun k => e.inv ≫ k) hd
    simpa [Category.assoc] using hh.symm
  have hcd : c * d = 1 := by
    apply (smul_left_injective ℂ (id_nonzero R))
    have hh := h
    rw [hg, hf] at hh
    simpa [Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc, mul_comm] using hh
  change mixedCrossingBilinear C X T T R S g f = _
  rw [hg, hf]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm d c, hcd, one_smul]
  rfl


end PropertyF.Ground.CentreInduction
