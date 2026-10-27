module
public import PropertyF.Ground.Dimensions.NaturalRoots
public import PropertyF.Ground.Dimensions.BiproductTrace

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Trace with the actual natural square root of the fourth dual, without
assuming that root is monoidal. -/
def rootTrace (C : Ground.BraidedFusionCategory.{v,u}) {X : C.Obj} (f : X ⟶ X) :
    End (𝟙_ C.Obj) := rightTraceWith ((fourthDualRootNaturalIso C).app X) f

set_option backward.isDefEq.respectTransparency false in
/-- The root trace is linear in its endomorphism. -/
def rootTraceLinear (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (X ⟶ X) →ₗ[ℂ] End (𝟙_ C.Obj) where
  toFun := rootTrace C
  map_add' := by
    intro f g
    apply End.homEquiv.injective
    simp [rootTrace, rightTraceWith, tensorHom_def]
  map_smul' := by
    intro z f
    apply End.homEquiv.injective
    simp [rootTrace, rightTraceWith, tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the square root makes its trace cyclic. -/
theorem rootTrace_cyclic (C : Ground.BraidedFusionCategory.{v,u}) {X Y : C.Obj}
    (f : X ⟶ Y) (g : Y ⟶ X) : rootTrace C (f ≫ g) = rootTrace C (g ≫ f) := by
  apply rightTraceWith_cyclic
  have h := (fourthDualRootNaturalIso C).hom.naturality f
  change f ≫ ((fourthDualRootNaturalIso C).app Y).hom =
    ((fourthDualRootNaturalIso C).app X).hom ≫ ((fᘁ)ᘁ) at h
  exact h

/-- The root trace of a finite biproduct is the sum of its diagonal block traces. -/
theorem rootTrace_biproduct (C : Ground.BraidedFusionCategory.{v,u})
    {ι : Type*} [Fintype ι] (F : ι → C.Obj) [HasBiproduct F]
    (f : (⨁ F) ⟶ (⨁ F)) :
    rootTrace C f = ∑ i, rootTrace C (biproduct.ι F i ≫ f ≫ biproduct.π F i) := by
  classical
  calc
    _ = rootTrace C ((∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ f) := by
      rw [biproduct.total]; simp
    _ = ∑ i, rootTrace C ((biproduct.π F i ≫ biproduct.ι F i) ≫ f) := by
      rw [Preadditive.sum_comp]
      exact map_sum (rootTraceLinear C _) _ _
    _ = ∑ i, rootTrace C (biproduct.ι F i ≫ f ≫ biproduct.π F i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Category.assoc]
      simpa only [Category.assoc] using rootTrace_cyclic C (biproduct.π F i) (biproduct.ι F i ≫ f)

/-- The natural-root trace of the identity is invariant under isomorphism. -/
theorem rootTrace_id_iso (C : Ground.BraidedFusionCategory.{v,u}) {X Y : C.Obj} (e : X ≅ Y) :
    rootTrace C (𝟙 X) = rootTrace C (𝟙 Y) := by
  simpa using rootTrace_cyclic C e.hom e.inv

/-- On a finite biproduct of simples, the natural-root trace is the sum of
simple dimensions weighted by the scalar diagonal blocks. -/
theorem rootTrace_biproduct_simple (C : Ground.BraidedFusionCategory.{v,u})
    {ι : Type*} [Fintype ι] (F : ι → C.Obj) [HasBiproduct F]
    (hs : ∀ i, Simple (F i)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → ℂ,
      (∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) ∧
      rootTrace C f = ∑ i, c i • rootTrace C (𝟙 (F i)) := by
  classical
  have h : ∀ i, ∃ c : ℂ, biproduct.ι F i ≫ f ≫ biproduct.π F i = c • 𝟙 (F i) := by
    intro i
    letI : Simple (F i) := hs i
    letI : FiniteDimensional ℂ (F i ⟶ F i) := Ground.IsFusionCategory.hom_finite _ _
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (biproduct.ι F i ≫ f ≫ biproduct.π F i)
    exact ⟨c, hc.symm⟩
  choose c hc using h
  refine ⟨c, hc, ?_⟩
  rw [rootTrace_biproduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i]
  exact (rootTraceLinear C (F i)).map_smul _ _

end PropertyF.Ground.Dimensions
