module
public import PropertyF.Ground.CentreInduction.WeakHalfBraiding
public import PropertyF.Ground.CentreInduction.BasisPairing

/-! Tensor-unit normalization for the explicit induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing CategoryTheory.Limits
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
-- Chosen simple representatives of the base category.
local notation "Sᶜ" => simples C
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable {T U S K R : D} (X : D)

section
variable (S : D) [HasRightDual S]

set_option backward.isDefEq.respectTransparency false in
/-- Closing the tensor-unit unitor gives the unitor of the dual object. -/
theorem closeFusionMap_unit :
    closeFusionMap (𝟙_ D) S (λ_ S).hom = (ρ_ (Sᘁ)).hom :=
  Dimensions.evaluation_ext (X := S) <| by
    rw [closeFusionMap_evaluation]
    monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit crossing block is the unitor comparison. -/
theorem crossingBlock_unit :
  crossingBlock X (𝟙_ D) S (λ_ S).inv (λ_ S).hom =
    (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv := by
  simp only [crossingBlock, mixedCrossing, closeFusionMap_unit]
  monoidal
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
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ T ◁ g) ⊗≫
      (closeFusionMap T K f ▷ K ≫ ε_ K (Kᘁ)) := by
      rw [closeFusionMap_evaluation]
      monoidal
    _ = 𝟙 _ ⊗≫ ((((Rᘁ : D) ⊗ T) ◁ g) ≫ (closeFusionMap T K f ▷ K)) ⊗≫ ε_ K (Kᘁ) := by monoidal
    _ = _ := by
      rw [whisker_exchange]
      simp only [monoidalComp, comp_whiskerRight, Category.assoc, closeFusionMap_evaluation]
      monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Two crossing blocks compose to the block of their composite fusion maps. -/
theorem crossingBlock_tensor
    (g₁ : R ⟶ T ⊗ K) (g₂ : K ⟶ U ⊗ S)
    (f₁ : T ⊗ K ⟶ R) (f₂ : U ⊗ S ⟶ K) :
  crossingBlock X (T ⊗ U) S (g₁ ≫ (T ◁ g₂) ≫ (α_ T U S).inv)
      ((α_ T U S).hom ≫ (T ◁ f₂) ≫ f₁) =
    𝟙 _ ⊗≫ (crossingBlock X T K g₁ f₁ ▷ U) ⊗≫
      (T ◁ crossingBlock X U S g₂ f₂) ⊗≫ 𝟙 _ := by
  let q := closeFusionMap T K f₁
  let z := closeFusionMap U S f₂
  calc
    _ = 𝟙 _ ⊗≫ (g₁ ▷ (X ⊗ (((Rᘁ : D) ⊗ T) ⊗ U))) ⊗≫
      ((((T ◁ g₂) ▷ X) ▷ (((Rᘁ : D) ⊗ T) ⊗ U)) ≫
        (((T ⊗ (U ⊗ S)) ⊗ X) ◁ (q ▷ U))) ⊗≫
      (((T ⊗ (U ⊗ S)) ⊗ X) ◁ z) ⊗≫ 𝟙 _ := by
        dsimp only [crossingBlock, mixedCrossing]
        rw [closeFusionMap_tensor, tensorHom_def, comp_whiskerRight]
        monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp only [crossingBlock, mixedCrossing]
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal
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
  obtain ⟨d, hd⟩ := CategoryTheory.endomorphism_simple_eq_smul_id k (e.hom ≫ f)
  have hg : g = c • e.hom := by
    simpa [Category.assoc] using (congrArg (fun k => k ≫ e.hom) hc).symm
  have hf : f = d • e.inv := by
    simpa [Category.assoc] using (congrArg (fun k => e.inv ≫ k) hd).symm
  have hcd : c * d = 1 := by
    apply (smul_left_injective k (id_nonzero R))
    simpa [hg, hf, Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc, mul_comm] using h
  change mixedCrossingBilinear (k := k) X T T R S g f = _
  simp only [hg, hf, map_smul, LinearMap.smul_apply, smul_smul, mul_comm d c, hcd, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a simple object, any splitting gives the same unit crossing block. -/
theorem crossingBlock_unit_of_split [HasRightDual S] [Simple S] [FiniteDimensional k (S ⟶ S)]
    (g : S ⟶ (𝟙_ D) ⊗ S) (f : (𝟙_ D) ⊗ S ⟶ S) (h : g ≫ f = 𝟙 S) :
    crossingBlock X (𝟙_ D) S g f =
      (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv :=
  (crossingBlock_of_simple_split (k := k) X (λ_ S).symm g f h).trans (crossingBlock_unit X S)

variable (X : C.Obj) (i j : Fin (rank C))

set_option backward.isDefEq.respectTransparency false in
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
    rw [Fintype.sum_unique]
    let : Simple (Sᶜ i) := simples_simple C i
    let : FiniteDimensional ℂ (Sᶜ i ⟶ Sᶜ i) := IsFusionCategory.hom_finite _ _
    rw [crossingBlock_unit_of_split (k := ℂ) X
      (crossingInclusion C (𝟙_ C.Obj) i i default) (crossingProjection C (𝟙_ C.Obj) i i default)
      (crossingInclusion_projection default), Category.assoc]
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
      crossingCandidate_unit_summand C X i

end PropertyF.Ground.CentreInduction
