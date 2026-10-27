module
public import PropertyF.Ground.CentreModular.ForgetTrace

/-! Diagonal-block expansion of the explicit induced Hopf link. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Trace of an endomorphism of a tensor-product biproduct as the sum of its
diagonal tensor blocks. -/
theorem trace_tensor_biproduct (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    {ι : Type*} [Fintype ι] (V : ι → C.Obj) (T : C.Obj)
    (f : (⨁ V) ⊗ T ⟶ (⨁ V) ⊗ T) :
    p.rightTrace f = ∑ i, p.rightTrace ((biproduct.ι V i ▷ T) ≫ f ≫ (biproduct.π V i ▷ T)) := by
  classical
  have ht : (∑ i, (biproduct.π V i ▷ T) ≫ (biproduct.ι V i ▷ T)) = 𝟙 ((⨁ V) ⊗ T) := by
    simp only [← comp_whiskerRight, ← sum_whiskerRight, biproduct.total, id_whiskerRight]
  calc
    _ = p.rightTrace ((∑ i, (biproduct.π V i ▷ T) ≫ (biproduct.ι V i ▷ T)) ≫ f) := by
      rw [ht, Category.id_comp]
    _ = ∑ i, p.rightTrace (((biproduct.π V i ▷ T) ≫ (biproduct.ι V i ▷ T)) ≫ f) := by
      rw [Preadditive.sum_comp]
      exact map_sum (Dimensions.rightTraceLinear p _) _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Category.assoc] using p.rightTrace_cyclic
        (biproduct.π V i ▷ T) ((biproduct.ι V i ▷ T) ≫ f)

/-- The closed induced crossing has only diagonal fusion-matrix blocks. -/
theorem induced_crossing_trace_diagonal (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj)
    (Z : CategoryTheory.Center C.Obj) :
    p.rightTrace (CentreInduction.crossingCandidate C X Z.1 ≫
      (Z.2.β (CentreInduction.underlying C X)).hom) =
    ∑ i, ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ Z.1 ⊗ simples C i)),
      p.rightTrace (CentreInduction.crossingBlock C X Z.1 (simples C i) (simples C i)
        (CentreInduction.crossingInclusion C Z.1 i i a)
        (CentreInduction.crossingProjection C Z.1 i i a) ≫
          (Z.2.β ((simples C i ⊗ X) ⊗ (simples C i)ᘁ)).hom) := by
  classical
  let V : Fin (rank C) → C.Obj := fun i => (simples C i ⊗ X) ⊗ (simples C i)ᘁ
  change p.rightTrace (CentreInduction.crossingCandidate C X Z.1 ≫ (Z.2.β (⨁ V)).hom) = _
  rw [trace_tensor_biproduct C p V Z.1]
  apply Finset.sum_congr rfl
  intro i _
  have hx := CentreInduction.crossingCandidate_on_summand C X Z.1 i
  change (biproduct.ι V i ▷ Z.1) ≫ CentreInduction.crossingCandidate C X Z.1 = _ at hx
  simp only [← Category.assoc]
  rw [hx]
  simp only [Preadditive.sum_comp]
  change (Dimensions.rightTraceLinear p _) (∑ j, ∑ a,
    ((CentreInduction.crossingBlock C X Z.1 (simples C i) (simples C j)
      (CentreInduction.crossingInclusion C Z.1 i j a)
      (CentreInduction.crossingProjection C Z.1 i j a) ≫ (Z.1 ◁ biproduct.ι V j)) ≫
      (Z.2.β (⨁ V)).hom) ≫ (biproduct.π V i ▷ Z.1)) = _
  simp only [map_sum]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Dimensions.rightTraceLinear, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    have hn := Z.2.naturality (biproduct.ι V i)
    simp only [Category.assoc]
    rw [← Category.assoc (Z.1 ◁ biproduct.ι V i), hn]
    simp only [Category.assoc, ← comp_whiskerRight, biproduct.ι_π_self, id_whiskerRight, Category.comp_id]
    rfl
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro a _
    simp only [Dimensions.rightTraceLinear, LinearMap.coe_mk, AddHom.coe_mk]
    have hzero : (biproduct.ι V j ▷ Z.1) ≫ (biproduct.π V i ▷ Z.1) = 0 := by
      rw [← comp_whiskerRight, biproduct.ι_π_ne _ hji, MonoidalPreadditive.zero_whiskerRight]
    have hn := Z.2.naturality (biproduct.ι V j)
    have hz : ((Z.1 ◁ biproduct.ι V j) ≫ (Z.2.β (⨁ V)).hom) ≫
        (biproduct.π V i ▷ Z.1) = 0 := by
      rw [hn, Category.assoc, hzero, comp_zero]
    have hf : (((CentreInduction.crossingBlock C X Z.1 (simples C i) (simples C j)
        (CentreInduction.crossingInclusion C Z.1 i j a)
        (CentreInduction.crossingProjection C Z.1 i j a) ≫ (Z.1 ◁ biproduct.ι V j)) ≫
          (Z.2.β (⨁ V)).hom) ≫ (biproduct.π V i ▷ Z.1)) = 0 := by
      simpa only [Category.assoc, comp_zero] using
        congrArg (fun q => CentreInduction.crossingBlock C X Z.1 (simples C i) (simples C j)
          (CentreInduction.crossingInclusion C Z.1 i j a)
          (CentreInduction.crossingProjection C Z.1 i j a) ≫ q) hz
    rw [hf]
    exact map_zero (Dimensions.rightTraceLinear p _)
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The FP-weighted centre Kirby sum is an explicit finite sum of base
pivotal traces of diagonal induction-crossing blocks. -/
theorem center_kirby_sum_eq_diagonal_traces
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (k : Fin (rank (Integrate.bundledCenter C)))
    (hcompat : ∀ i, let X := (CentreInduction.induction C).obj (simples C i)
      let Y := simples (Integrate.bundledCenter C) k
      ((pZ.iso (X ⊗ Y)).hom.f) ≫ (CentreInduction.forgetDoubleDualIso C (X ⊗ Y)).hom =
        (p.iso (X.1 ⊗ Y.1)).hom) :
    (∑ j, (fpSimple (Integrate.bundledCenter C) j : ℂ) *
      Modular.categoricalS (Integrate.bundledCenter C) pZ j k) =
    ∑ i, (fpSimple C i : ℂ) * ∑ j,
      ∑ a : Fin (Module.finrank ℂ (simples C j ⟶
        (simples (Integrate.bundledCenter C) k).1 ⊗ simples C j)),
      unitScalar C (p.rightTrace
        (CentreInduction.crossingBlock C (simples C i) (simples (Integrate.bundledCenter C) k).1
          (simples C j) (simples C j)
          (CentreInduction.crossingInclusion C (simples (Integrate.bundledCenter C) k).1 j j a)
          (CentreInduction.crossingProjection C (simples (Integrate.bundledCenter C) k).1 j j a) ≫
        (((simples (Integrate.bundledCenter C) k).2.β
          ((simples C j ⊗ simples C i) ⊗ (simples C j)ᘁ)).hom))) := by
  rw [center_kirby_sum_eq_base_traces C p pZ k hcompat]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [induced_crossing_trace_diagonal C p (simples C i) (simples (Integrate.bundledCenter C) k)]
  simp only [unitScalar_eq_equiv, map_sum]

end PropertyF.Ground.CentreModular
