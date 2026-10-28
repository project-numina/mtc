module
public import PropertyF.Ground.CentreInduction.BasisPairing

/-! Tensor-unit normalization for the explicit induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing CategoryTheory.Limits
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
attribute [local instance] IsFusionCategory.hom_finite
variable {C : BraidedFusionCategory.{v,u}}
-- Chosen simple representatives of the base category.
local notation "Sᶜ" => simples C
local instance (i : Fin (rank C)) : Simple (Sᶜ i) := simples_simple C i
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable {T U S K R : D} (X : D)

section
variable (S : D) [HasRightDual S]

set_option backward.isDefEq.respectTransparency false in
/-- Closing the tensor-unit unitor gives the unitor of the dual object. -/
theorem closeFusionMap_unit :
    closeFusionMap (𝟙_ D) S (λ_ S).hom = (ρ_ (Sᘁ)).hom :=
  Dimensions.evaluation_ext (X := S) <| by
    simp [closeFusionMap_evaluation, monoidalComp]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit crossing block is the unitor comparison. -/
theorem crossingBlock_unit :
  crossingBlock X (𝟙_ D) S (λ_ S).inv (λ_ S).hom =
    (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv := by
  simp [crossingBlock, mixedCrossing, closeFusionMap_unit, tensorHom_def, Category.assoc]
end

section
variable [HasRightDual R] [HasRightDual K] [HasRightDual S]

set_option backward.isDefEq.respectTransparency false in
/-- Closing a composite fusion map is the composite of the two closed maps. -/
theorem closeFusionMap_tensor (f : T ⊗ K ⟶ R) (g : U ⊗ S ⟶ K) :
  closeFusionMap (T ⊗ U) S ((α_ T U S).hom ≫ (T ◁ g) ≫ f) =
    𝟙 _ ⊗≫ (closeFusionMap T K f ▷ U) ⊗≫ closeFusionMap U S g := by
  apply Dimensions.evaluation_ext (X := S)
  rw [closeFusionMap_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ ((((Rᘁ : D) ⊗ T) ◁ g) ≫ (closeFusionMap T K f ▷ K)) ⊗≫ ε_ K (Kᘁ) := by
      simp [closeFusionMap_evaluation, monoidalComp]
    _ = _ := by
      rw [whisker_exchange]
      simp [monoidalComp, comp_whiskerRight, Category.assoc, closeFusionMap_evaluation]

set_option backward.isDefEq.respectTransparency false in
/-- Two crossing blocks compose to the block of their composite fusion maps. -/
theorem crossingBlock_tensor
    (g₁ : R ⟶ T ⊗ K) (g₂ : K ⟶ U ⊗ S)
    (f₁ : T ⊗ K ⟶ R) (f₂ : U ⊗ S ⟶ K) :
  crossingBlock X (T ⊗ U) S (g₁ ≫ (T ◁ g₂) ≫ (α_ T U S).inv)
      ((α_ T U S).hom ≫ (T ◁ f₂) ≫ f₁) =
    𝟙 _ ⊗≫ (crossingBlock X T K g₁ f₁ ▷ U) ⊗≫
      (T ◁ crossingBlock X U S g₂ f₂) ⊗≫ 𝟙 _ := by
  dsimp only [crossingBlock, mixedCrossing]
  rw [closeFusionMap_tensor]
  simp only [tensorHom_def, comp_whiskerRight]
  convert congrArg (fun h : (((T ⊗ K) ⊗ X) ⊗ (((Rᘁ : D) ⊗ T) ⊗ U) ⟶
      ((T ⊗ (U ⊗ S)) ⊗ X) ⊗ ((Kᘁ : D) ⊗ U)) =>
    𝟙 (((R ⊗ X) ⊗ Rᘁ) ⊗ (T ⊗ U)) ⊗≫
      (g₁ ▷ (X ⊗ (((Rᘁ : D) ⊗ T) ⊗ U))) ⊗≫ h ⊗≫
      (((T ⊗ (U ⊗ S)) ⊗ X) ◁ closeFusionMap U S f₂) ⊗≫
        𝟙 ((T ⊗ U) ⊗ ((S ⊗ X) ⊗ Sᘁ)))
    (whisker_exchange ((T ◁ g₂) ▷ X) (closeFusionMap T K f₁ ▷ U)).symm using 1 <;> monoidal

end

variable {k : Type*} [Field k] [IsAlgClosed k] [Preadditive D] [Linear k D]
  [MonoidalPreadditive D] [MonoidalLinear k D] [HasKernels D]

set_option backward.isDefEq.respectTransparency false in
/-- A split crossing block is independent of the chosen splitting of a simple. -/
theorem crossingBlock_of_simple_split [HasRightDual R] [HasRightDual S] [Simple R]
    [FiniteDimensional k (R ⟶ R)]
    (e : R ≅ T ⊗ S) (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) (h : g ≫ f = 𝟙 R) :
    crossingBlock X T S g f = crossingBlock X T S e.hom e.inv := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id k (g ≫ e.inv)
  have hg : g = c • e.hom := by
    simpa [Category.assoc] using (congrArg (fun k => k ≫ e.hom) hc).symm
  have hc0 : c ≠ 0 := fun hc0 => id_nonzero R (by simpa [hg, hc0] using h.symm)
  have hf : f = c⁻¹ • e.inv := by
    simpa [hg, ← Category.assoc, Linear.comp_smul, Linear.smul_comp, smul_smul, hc0] using
      congrArg (fun k => c⁻¹ • (e.inv ≫ k)) h
  change mixedCrossingBilinear (k := k) X T T R S g f =
    mixedCrossingBilinear (k := k) X T T R S e.hom e.inv
  simp [hg, hf, hc0]

variable (X : C.Obj) (i j : Fin (rank C))

set_option backward.isDefEq.respectTransparency false in
variable (C) in
/-- The unit-strand decomposition has one diagonal simple summand. -/
theorem unit_crossing_finrank :
    Module.finrank ℂ (Sᶜ i ⟶ (𝟙_ C.Obj) ⊗ Sᶜ j) = if i = j then 1 else 0 :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (λ_ (Sᶜ j))).finrank_eq.trans
    (finrank_simples_hom C i j)

set_option backward.isDefEq.respectTransparency false in
/-- The unit crossing on each induction summand is the canonical unitor map. -/
theorem crossingCandidate_unit_summand :
    let V := inductionSummand C X
    (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ crossingCandidate C X (𝟙_ C.Obj) =
      (ρ_ (V i)).hom ≫ (λ_ (V i)).inv ≫ ((𝟙_ C.Obj) ◁ biproduct.ι V i) := by
  simp only [crossingCandidate_on_summand, crossingSummand]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · let : Unique (crossingIndex C (𝟙_ C.Obj) i i) := by
      simpa only [crossingIndex, unit_crossing_finrank, ↓reduceIte] using
        (inferInstance : Unique (Fin 1))
    rw [Fintype.sum_unique, crossingBlock_of_simple_split (k := ℂ) X (λ_ (Sᶜ i)).symm
      (crossingInclusion C (𝟙_ C.Obj) i i default) (crossingProjection C (𝟙_ C.Obj) i i default)
      (crossingInclusion_projection default)]
    erw [crossingBlock_unit, Category.assoc]
  · intro j _ hne
    let : IsEmpty (crossingIndex C (𝟙_ C.Obj) i j) := by
      simpa only [crossingIndex, unit_crossing_finrank, Ne.symm hne, ↓reduceIte] using
        (inferInstance : IsEmpty (Fin 0))
    exact Fintype.sum_empty _

set_option backward.isDefEq.respectTransparency false in
/-- The explicit induction crossing is normalized on the tensor unit. -/
theorem crossingCandidate_unit :
    crossingCandidate C X (𝟙_ C.Obj) =
      (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv :=
  rightDistributor_ext_left (f := inductionSummand C X) fun i => by
    simpa only [underlying, ← leftUnitor_inv_naturality, rightUnitor_naturality_assoc] using
      crossingCandidate_unit_summand X i

end PropertyF.Ground.CentreInduction
