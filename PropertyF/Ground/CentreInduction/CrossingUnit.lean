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

set_option backward.isDefEq.respectTransparency false in
/-- The closed fusion map is characterized by its evaluation pairing. -/
theorem closeFusionMap_evaluation {T S R : D} (f : T ⊗ S ⟶ R) :
    (closeFusionMap T S f ▷ S) ≫ ε_ S (Sᘁ) =
      𝟙 _ ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ) := by
  have he := PropertyF.Ground.Dimensions.rightDualIso_evaluation
      (@HasRightDual.exact D _ _ (T ⊗ S) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := T) (X₂ := S) (Y₁ := Tᘁ) (Y₂ := Sᘁ))
  change (rightDualTensorIso T S).hom ▷ (T ⊗ S) ≫
    ε_ (T ⊗ S) ((Sᘁ) ⊗ (Tᘁ)) = ε_ (T ⊗ S) ((T ⊗ S)ᘁ) at he
  change (rightDualTensorIso T S).hom ▷ (T ⊗ S) ≫
    (𝟙 _ ⊗≫ (Sᘁ) ◁ (ε_ T (Tᘁ) ▷ S) ⊗≫ ε_ S (Sᘁ)) =
      ε_ (T ⊗ S) ((T ⊗ S)ᘁ) at he
  calc
    _ = 𝟙 _ ⊗≫ ((fᘁ) ▷ (T ⊗ S)) ⊗≫
      ((rightDualTensorIso T S).hom ▷ (T ⊗ S)) ⊗≫
      ((Sᘁ) ◁ (ε_ T (Tᘁ) ▷ S)) ⊗≫ ε_ S (Sᘁ) := by
      dsimp [closeFusionMap]; monoidal
    _ = 𝟙 _ ⊗≫ (fᘁ ▷ (T ⊗ S)) ⊗≫
      ((rightDualTensorIso T S).hom ▷ (T ⊗ S) ≫
        (𝟙 _ ⊗≫ (Sᘁ) ◁ (ε_ T (Tᘁ) ▷ S) ⊗≫ ε_ S (Sᘁ))) := by monoidal
    _ = 𝟙 _ ⊗≫ (fᘁ ▷ (T ⊗ S)) ⊗≫ ε_ (T ⊗ S) ((T ⊗ S)ᘁ) := by rw [he]
    _ = 𝟙 _ ⊗≫ ((fᘁ ▷ (T ⊗ S)) ≫ ε_ (T ⊗ S) ((T ⊗ S)ᘁ)) := by monoidal
    _ = _ := by rw [rightAdjointMate_comp_evaluation]; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Closing the tensor-unit unitor gives the unitor of the dual object. -/
theorem closeFusionMap_unit (S : D) :
    closeFusionMap (𝟙_ D) S (λ_ S).hom = (ρ_ (Sᘁ)).hom := by
  apply Dimensions.evaluation_ext (X := S)
  rw [closeFusionMap_evaluation]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit crossing block is the unitor comparison. -/
theorem crossingBlock_unit (X S : D) :
  crossingBlock X (𝟙_ D) S (λ_ S).inv (λ_ S).hom =
    (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv := by
  dsimp only [crossingBlock]
  rw [closeFusionMap_unit S]
  simp only [tensorHom_def]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Closing a composite fusion map is the composite of the two closed maps. -/
theorem closeFusionMap_tensor {T U S K R : D} (f : T ⊗ K ⟶ R) (g : U ⊗ S ⟶ K) :
  closeFusionMap (T ⊗ U) S ((α_ T U S).hom ≫ (T ◁ g) ≫ f) =
    𝟙 _ ⊗≫ (closeFusionMap T K f ▷ U) ⊗≫ closeFusionMap U S g := by
  apply Dimensions.evaluation_ext (X := S)
  rw [closeFusionMap_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ ((α_ T U S).hom ≫ (T ◁ g) ≫ f)) ⊗≫ ε_ R (Rᘁ) := rfl
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ T ◁ g) ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ) := by
      simp only [whiskerLeft_comp]; monoidal
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ T ◁ g) ⊗≫
      (𝟙 (((Rᘁ : D) ⊗ T) ⊗ K) ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ T ◁ g) ⊗≫
      (closeFusionMap T K f ▷ K ≫ ε_ K (Kᘁ)) := by rw [closeFusionMap_evaluation]
    _ = 𝟙 _ ⊗≫ ((((Rᘁ : D) ⊗ T) ◁ g) ≫ (closeFusionMap T K f ▷ K)) ⊗≫ ε_ K (Kᘁ) := by monoidal
    _ = 𝟙 _ ⊗≫ ((closeFusionMap T K f ▷ (U ⊗ S)) ≫ ((Kᘁ : D) ◁ g)) ⊗≫ ε_ K (Kᘁ) := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (closeFusionMap T K f ▷ (U ⊗ S)) ⊗≫
      (𝟙 (((Kᘁ : D) ⊗ U) ⊗ S) ⊗≫ ((Kᘁ : D) ◁ g) ⊗≫ ε_ K (Kᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ (closeFusionMap T K f ▷ (U ⊗ S)) ⊗≫
      (closeFusionMap U S g ▷ S ≫ ε_ S (Sᘁ)) := by rw [closeFusionMap_evaluation]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Two crossing blocks compose to the block of their composite fusion maps. -/
theorem crossingBlock_tensor (X : D) {T U S K R : D}
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
        dsimp only [crossingBlock]
        rw [closeFusionMap_tensor]
        simp only [tensorHom_def, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (g₁ ▷ (X ⊗ (((Rᘁ : D) ⊗ T) ⊗ U))) ⊗≫
      (((((T ⊗ K) ⊗ X) ◁ (q ▷ U))) ≫
        (((T ◁ g₂) ▷ X) ▷ ((Kᘁ : D) ⊗ U))) ⊗≫
      (((T ⊗ (U ⊗ S)) ⊗ X) ◁ z) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by
      dsimp only [crossingBlock]
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D]

set_option backward.isDefEq.respectTransparency false in
/-- A split crossing block is independent of the chosen splitting of a simple. -/
theorem crossingBlock_of_simple_split (X : D) {T R S : D} [Simple R]
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
    have hh := h
    rw [hg, hf] at hh
    simpa [Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc, mul_comm] using hh
  change mixedCrossingBilinear (k := ℂ) X T T R S g f = _
  rw [hg, hf]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm d c, hcd, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a simple object, any splitting gives the same unit crossing block. -/
theorem crossingBlock_unit_of_split (X : D) {S : D} [Simple S]
    [FiniteDimensional ℂ (S ⟶ S)]
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
/-- The explicit induction crossing is normalized on the tensor unit. -/
theorem crossingCandidate_unit (X : C.Obj) :
    crossingCandidate C X (𝟙_ C.Obj) =
      (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv := by
  classical
  let V := inductionSummand C X
  apply (cancel_epi (rightDistributor V (𝟙_ C.Obj)).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  change (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ crossingCandidate C X (𝟙_ C.Obj) =
    (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv
  rw [crossingCandidate_on_summand]
  dsimp only [crossingSummand]
  rw [Finset.sum_eq_single i]
  · have hdim : Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C i) = 1 := by
      rw [unit_crossing_finrank]; simp
    let a : crossingIndex C (𝟙_ C.Obj) i i := ⟨0, by rw [hdim]; decide⟩
    let : Subsingleton (crossingIndex C (𝟙_ C.Obj) i i) := by
      simp only [crossingIndex, hdim]
      infer_instance
    let : Unique (crossingIndex C (𝟙_ C.Obj) i i) :=
      ⟨⟨a⟩, fun b => Subsingleton.elim b a⟩
    rw [Fintype.sum_unique, show (default : crossingIndex C (𝟙_ C.Obj) i i) = a from Subsingleton.elim _ _]
    let : Simple (simples C i) := simples_simple C i
    let : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
    rw [crossingBlock_unit_of_split X
      (crossingInclusion C (𝟙_ C.Obj) i i a) (crossingProjection C (𝟙_ C.Obj) i i a)
      (crossingInclusion_projection a)]
    change ((ρ_ (V i)).hom ≫ (λ_ (V i)).inv) ≫ ((𝟙_ C.Obj) ◁ biproduct.ι V i) =
      (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ (ρ_ (⨁ V)).hom ≫ (λ_ (⨁ V)).inv
    simp only [Category.assoc, ← leftUnitor_inv_naturality, rightUnitor_naturality_assoc]
  · intro j _ hne
    have hdim : Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C j) = 0 := by
      rw [unit_crossing_finrank]; simp [Ne.symm hne]
    let : IsEmpty (crossingIndex C (𝟙_ C.Obj) i j) := by
      simp only [crossingIndex, hdim]
      infer_instance
    exact Finset.sum_eq_zero fun a _ => isEmptyElim a
  · simp

end PropertyF.Ground.CentreInduction
