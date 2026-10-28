module
public import PropertyF.Ground.CentreInduction.WeakHalfBraiding

/-! Tensor-unit normalization for the explicit induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing CategoryTheory.Limits
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
variable {T U S K R : D} (X : D)

set_option backward.isDefEq.respectTransparency false in
/-- Closing the tensor-unit unitor gives the unitor of the dual object. -/
theorem closeFusionMap_unit (S : D) :
    closeFusionMap (𝟙_ D) S (λ_ S).hom = (ρ_ (Sᘁ)).hom := by
  apply Dimensions.evaluation_ext (X := S)
  rw [closeFusionMap_evaluation]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit crossing block is the unitor comparison. -/
theorem crossingBlock_unit (S : D) :
  crossingBlock X (𝟙_ D) S (λ_ S).inv (λ_ S).hom =
    (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv := by
  dsimp only [crossingBlock, mixedCrossing]
  rw [closeFusionMap_unit]
  monoidal

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

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D]

set_option backward.isDefEq.respectTransparency false in
/-- A split crossing block is independent of the chosen splitting of a simple. -/
theorem crossingBlock_of_simple_split [Simple R]
    [FiniteDimensional ℂ (R ⟶ R)]
    (e : R ≅ T ⊗ S) (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) (h : g ≫ f = 𝟙 R) :
    crossingBlock X T S g f = crossingBlock X T S e.hom e.inv := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (g ≫ e.inv)
  obtain ⟨d, hd⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (e.hom ≫ f)
  have hg : g = c • e.hom := by
    simpa [Category.assoc] using (congrArg (fun k => k ≫ e.hom) hc).symm
  have hf : f = d • e.inv := by
    simpa [Category.assoc] using (congrArg (fun k => e.inv ≫ k) hd).symm
  have hcd : c * d = 1 := by
    apply (smul_left_injective ℂ (id_nonzero R))
    simpa [hg, hf, Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc, mul_comm] using h
  change mixedCrossingBilinear (k := ℂ) X T T R S g f = _
  simp only [hg, hf, map_smul, LinearMap.smul_apply, smul_smul, mul_comm d c, hcd, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a simple object, any splitting gives the same unit crossing block. -/
theorem crossingBlock_unit_of_split [Simple S] [FiniteDimensional ℂ (S ⟶ S)]
    (g : S ⟶ (𝟙_ D) ⊗ S) (f : (𝟙_ D) ⊗ S ⟶ S) (h : g ≫ f = 𝟙 S) :
    crossingBlock X (𝟙_ D) S g f =
      (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv :=
  (crossingBlock_of_simple_split X (λ_ S).symm g f h).trans (crossingBlock_unit X S)

set_option backward.isDefEq.respectTransparency false in
/-- The unit-strand decomposition has one diagonal simple summand. -/
theorem unit_crossing_finrank (i j : Fin (rank C)) :
    Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C j) = if i = j then 1 else 0 :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (λ_ (simples C j))).finrank_eq.trans
    (finrank_simples_hom C i j)

set_option backward.isDefEq.respectTransparency false in
/-- The unit crossing on each induction summand is the canonical unitor map. -/
theorem crossingCandidate_unit_summand (X : C.Obj) (i : Fin (rank C)) :
    let V := inductionSummand C X
    (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ crossingCandidate C X (𝟙_ C.Obj) =
      (ρ_ (V i)).hom ≫ (λ_ (V i)).inv ≫ ((𝟙_ C.Obj) ◁ biproduct.ι V i) := by
  dsimp only
  rw [crossingCandidate_on_summand]
  dsimp only [crossingSummand]
  rw [Finset.sum_eq_single i]
  · let : Unique (crossingIndex C (𝟙_ C.Obj) i i) := by
      simpa only [crossingIndex, unit_crossing_finrank, ↓reduceIte] using
        (inferInstance : Unique (Fin 1))
    rw [Fintype.sum_unique]
    let : Simple (simples C i) := simples_simple C i
    let : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
    rw [crossingBlock_unit_of_split X
      (crossingInclusion C (𝟙_ C.Obj) i i default) (crossingProjection C (𝟙_ C.Obj) i i default)
      (crossingInclusion_projection default), Category.assoc]
  · intro j _ hne
    let : IsEmpty (crossingIndex C (𝟙_ C.Obj) i j) := by
      simpa only [crossingIndex, unit_crossing_finrank, Ne.symm hne, ↓reduceIte] using
        (inferInstance : IsEmpty (Fin 0))
    exact Finset.sum_eq_zero fun a _ => isEmptyElim a
  · exact fun hi => (hi (Finset.mem_univ i)).elim

set_option backward.isDefEq.respectTransparency false in
/-- The explicit induction crossing is normalized on the tensor unit. -/
theorem crossingCandidate_unit (X : C.Obj) :
    crossingCandidate C X (𝟙_ C.Obj) =
      (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv := by
  let V := inductionSummand C X
  refine rightDistributor_ext_left (f := V) fun i => ?_
  rw [crossingCandidate_unit_summand]
  dsimp only [underlying, V]
  rw [← leftUnitor_inv_naturality, rightUnitor_naturality_assoc]

end PropertyF.Ground.CentreInduction
