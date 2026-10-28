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
    (closeFusionMap T S R f ▷ S) ≫ ε_ S (Sᘁ) =
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
/-- A map to a right dual is determined by its evaluation. -/
theorem dual_map_ext {V : D} (S : D) (f g : V ⟶ Sᘁ)
    (h : f ▷ S ≫ ε_ S (Sᘁ) = g ▷ S ≫ ε_ S (Sᘁ)) : f = g := by
  apply (cancel_mono (λ_ (Sᘁ)).inv).1
  simpa only [tensorRightHomEquiv_whiskerRight_comp_evaluation] using
    congrArg (tensorRightHomEquiv V S (Sᘁ) (𝟙_ D)) h

set_option backward.isDefEq.respectTransparency false in
/-- Closing the tensor-unit unitor gives the unitor of the dual object. -/
theorem closeFusionMap_unit (S : D) :
    closeFusionMap (𝟙_ D) S S (λ_ S).hom = (ρ_ (Sᘁ)).hom := by
  apply dual_map_ext S
  rw [closeFusionMap_evaluation]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit crossing block is the unitor comparison. -/
theorem crossingBlock_unit (X S : D) :
  crossingBlock X (𝟙_ D) S S (λ_ S).inv (λ_ S).hom =
    (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv := by
  dsimp only [crossingBlock]
  rw [closeFusionMap_unit S]
  simp only [tensorHom_def]
  monoidal

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D]

set_option backward.isDefEq.respectTransparency false in
/-- A split crossing block is independent of the chosen splitting of a simple. -/
theorem crossingBlock_of_simple_split (X T : D) {R S : D} [Simple R]
    [FiniteDimensional ℂ (R ⟶ R)]
    (e : R ≅ T ⊗ S) (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) (h : g ≫ f = 𝟙 R) :
    crossingBlock X T R S g f = crossingBlock X T R S e.hom e.inv := by
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
    crossingBlock X (𝟙_ D) S S g f =
      (ρ_ ((S ⊗ X) ⊗ Sᘁ)).hom ≫ (λ_ ((S ⊗ X) ⊗ Sᘁ)).inv :=
  (crossingBlock_of_simple_split X (𝟙_ D) (λ_ S).symm g f h).trans (crossingBlock_unit X S)

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
    let : Subsingleton (Fin (Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C i))) := by
      rw [hdim]
      infer_instance
    let : Unique (Fin (Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C i))) :=
      ⟨⟨a⟩, fun b => Subsingleton.elim b a⟩
    rw [Fintype.sum_unique, show (default : Fin (Module.finrank ℂ
      (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C i))) = a from Subsingleton.elim _ _]
    let : Simple (simples C i) := simples_simple C i
    let : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
    rw [crossingBlock_unit_of_split X
      (crossingInclusion C (𝟙_ C.Obj) i i a) (crossingProjection C (𝟙_ C.Obj) i i a)
      (crossingInclusion_projection C (𝟙_ C.Obj) i i a)]
    change ((ρ_ (V i)).hom ≫ (λ_ (V i)).inv) ≫ ((𝟙_ C.Obj) ◁ biproduct.ι V i) =
      (biproduct.ι V i ▷ (𝟙_ C.Obj)) ≫ (ρ_ (⨁ V)).hom ≫ (λ_ (⨁ V)).inv
    simp only [Category.assoc, ← leftUnitor_inv_naturality, rightUnitor_naturality_assoc]
  · intro j _ hne
    have hdim : Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C j) = 0 := by
      rw [unit_crossing_finrank]; simp [Ne.symm hne]
    let : IsEmpty (Fin (Module.finrank ℂ (simples C i ⟶ (𝟙_ C.Obj) ⊗ simples C j))) := by
      rw [hdim]
      infer_instance
    exact Finset.sum_eq_zero fun a _ => isEmptyElim a
  · simp

end PropertyF.Ground.CentreInduction
