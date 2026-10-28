module
public import PropertyF.Ground.CentreInduction.WeakHalfBraiding

/-! Tensor-unit normalization for the explicit induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing CategoryTheory.Limits
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- The closed fusion map is characterized by its evaluation pairing. -/
theorem closeFusionMap_evaluation (T S R : C.Obj) (f : T ⊗ S ⟶ R) :
    (closeFusionMap C T S R f ▷ S) ≫ ε_ S (Sᘁ) =
      𝟙 _ ⊗≫ ((Rᘁ : C.Obj) ◁ f) ⊗≫ ε_ R (Rᘁ) := by
  have he := PropertyF.Ground.Dimensions.rightDualIso_evaluation
      (@HasRightDual.exact C.Obj _ _ (T ⊗ S) (RightRigidCategory.rightDual _))
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
theorem closeFusionMap_unit (S : C.Obj) :
    closeFusionMap C (𝟙_ C.Obj) S S (λ_ S).hom = (ρ_ (Sᘁ)).hom := by
  let f := closeFusionMap C (𝟙_ C.Obj) S S (λ_ S).hom
  let g := (ρ_ (Sᘁ)).hom
  have h : (f ▷ S) ≫ ε_ S (Sᘁ) = (g ▷ S) ≫ ε_ S (Sᘁ) := by
    rw [show f = closeFusionMap C (𝟙_ C.Obj) S S (λ_ S).hom from rfl, closeFusionMap_evaluation]
    dsimp [g]
    monoidal
  have he := congrArg (tensorRightHomEquiv ((Sᘁ) ⊗ (𝟙_ C.Obj)) S (Sᘁ) (𝟙_ C.Obj)) h
  have hf := @tensorRightHomEquiv_whiskerRight_comp_evaluation C.Obj _ _ S
    ((Sᘁ) ⊗ (𝟙_ C.Obj)) (RightRigidCategory.rightDual S) f
  have hg := @tensorRightHomEquiv_whiskerRight_comp_evaluation C.Obj _ _ S
    ((Sᘁ) ⊗ (𝟙_ C.Obj)) (RightRigidCategory.rightDual S) g
  change (tensorRightHomEquiv ((Sᘁ) ⊗ (𝟙_ C.Obj)) S (Sᘁ) (𝟙_ C.Obj))
    (f ▷ S ≫ ε_ S (Sᘁ)) = f ≫ (λ_ (Sᘁ)).inv at hf
  change (tensorRightHomEquiv ((Sᘁ) ⊗ (𝟙_ C.Obj)) S (Sᘁ) (𝟙_ C.Obj))
    (g ▷ S ≫ ε_ S (Sᘁ)) = g ≫ (λ_ (Sᘁ)).inv at hg
  rw [hf, hg] at he
  exact (cancel_mono (λ_ (Sᘁ)).inv).1 he

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit crossing block is the unitor comparison. -/
theorem crossingBlock_unit (X S : C.Obj) :
  crossingBlock C X (𝟙_ C.Obj) S S (λ_ S).inv (λ_ S).hom =
    (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv := by
  dsimp only [crossingBlock]
  rw [closeFusionMap_unit C S]
  simp only [tensorHom_def]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- For a simple object, any splitting gives the same unit crossing block. -/
theorem crossingBlock_unit_of_split (X S : C.Obj) [Simple S]
    (g : S ⟶ (𝟙_ C.Obj) ⊗ S) (f : (𝟙_ C.Obj) ⊗ S ⟶ S) (h : g ≫ f = 𝟙 S) :
    crossingBlock C X (𝟙_ C.Obj) S S g f =
      (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv := by
  let : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (g ≫ (λ_ S).hom)
  obtain ⟨d, hd⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ ((λ_ S).inv ≫ f)
  have hg : g = c • (λ_ S).inv := by
    have hh := congrArg (fun k => k ≫ (λ_ S).inv) hc
    simpa [Category.assoc] using hh.symm
  have hf : f = d • (λ_ S).hom := by
    have hh := congrArg (fun k => (λ_ S).hom ≫ k) hd
    simpa [Category.assoc] using hh.symm
  have hcd : c * d = 1 := by
    apply (smul_left_injective ℂ (id_nonzero S))
    have hh := h
    rw [hg, hf] at hh
    simpa [Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc, mul_comm] using hh
  change mixedCrossingBilinear C X (𝟙_ C.Obj) (𝟙_ C.Obj) S S g f = _
  rw [hg, hf]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm d c, hcd, one_smul]
  exact crossingBlock_unit C X S

set_option backward.isDefEq.respectTransparency false in
/-- The unit-strand decomposition has one diagonal simple summand. -/
theorem unit_crossing_finrank (i j : Fin (rank C)) :
    Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C j) = if i = j then 1 else 0 := by
  rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (λ_ (simples C j))).finrank_eq]
  exact finrank_simples_hom C i j

set_option backward.isDefEq.respectTransparency false in
/-- The explicit induction crossing is normalized on the tensor unit. -/
theorem crossingCandidate_unit (X : C.Obj) :
    crossingCandidate C X (𝟙_ C.Obj) =
      (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv := by
  classical
  let V : Fin (rank C) → C.Obj := fun i => (simples C i ⊗ X) ⊗ (simples C i)ᘁ
  apply (cancel_epi (rightDistributor V (𝟙_ C.Obj)).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  change (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ crossingCandidate C X (𝟙_ C.Obj) =
    (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ (ρ_ (underlying C X)).hom ≫ (λ_ (underlying C X)).inv
  rw [crossingCandidate_on_summand]
  rw [Finset.sum_eq_single i]
  · have hdim : Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C i) = 1 := by
      rw [unit_crossing_finrank]; simp
    let a : Fin (Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C i)) := ⟨0, by rw [hdim]; decide⟩
    have ha (b : Fin (Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C i))) : b = a := by
      apply Fin.ext
      have hb := b.isLt
      dsimp [a]
      omega
    rw [Finset.sum_eq_single a]
    · let : Simple (simples C i) := simples_simple C i
      rw [crossingBlock_unit_of_split C X (simples C i)
        (crossingInclusion C (𝟙_ C.Obj) i i a) (crossingProjection C (𝟙_ C.Obj) i i a)
        (crossingInclusion_projection C (𝟙_ C.Obj) i i a)]
      change ((ρ_ (V i)).hom ≫ (λ_ (V i)).inv) ≫ ((𝟙_ C.Obj) ◁ biproduct.ι V i) =
        (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ (ρ_ (⨁ V)).hom ≫ (λ_ (⨁ V)).inv
      simp only [Category.assoc, ← leftUnitor_inv_naturality, rightUnitor_naturality_assoc]
    · intro b _ hne
      exact (hne (ha b)).elim
    · simp
  · intro j _ hne
    have hdim : Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C j) = 0 := by
      rw [unit_crossing_finrank]; simp [Ne.symm hne]
    apply Finset.sum_eq_zero
    intro a _
    have ht := a.isLt
    omega
  · simp

end PropertyF.Ground.CentreInduction
