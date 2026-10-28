module
public import PropertyF.Ground.CentreInduction.CrossingBlocks
public import PropertyF.Ground.Dimensions.SimpleHomBasis
public import Mathlib.LinearAlgebra.Dual.Basis
public import PropertyF.Ground.Dimensions.DualTensorNaturality

open PropertyF.Ground.Dimensions

/-! Dual bases for the actual fusion summand inclusions and projections. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The perfect pairing is natural for maps between different underlying
objects: precomposition corresponds to dualizing postcomposition. -/
theorem simpleHomPairingEquiv_natural (i : Fin (rank C)) {V W : C.Obj} (q : V ⟶ W)
    (f : W ⟶ simples C i) : simpleHomPairingEquiv C i V (q ≫ f) =
    Module.Dual.transpose (Linear.rightComp ℂ (simples C i) q) (simpleHomPairingEquiv C i W f) := by
  ext g
  simp [simpleHomPairingEquiv, simpleHomPairing,
    Module.Dual.transpose_apply, Linear.rightComp_apply, Category.assoc]

/-- A bilinear contraction with dual bases is natural under any linear map.
This is the matrix identity needed to change fusion bases across a morphism. -/
theorem dualBasis_contraction_natural {k : Type*} [CommSemiring k] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {A B E : Type*} [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    [AddCommMonoid E] [Module k E] (a : Module.Basis I k A) (b : Module.Basis J k B)
    (L : A →ₗ[k] B) (F : B →ₗ[k] Module.Dual k A →ₗ[k] E) :
    (∑ i, F (L (a i)) (a.dualBasis i)) =
      ∑ j, F (b j) (Module.Dual.transpose L (b.dualBasis j)) := by
  let c : I → J → k := fun i j => b.repr (L (a i)) j
  have hL (i : I) : L (a i) = ∑ j, c i j • b j := (b.sum_repr _).symm
  have hD (j : J) : Module.Dual.transpose L (b.dualBasis j) =
      ∑ i, c i j • a.dualBasis i := by
    simpa [c, Module.Basis.dualBasis_repr, Module.Dual.transpose_apply] using
      (a.dualBasis.sum_repr (Module.Dual.transpose L (b.dualBasis j))).symm
  simp only [hL, hD, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm

set_option backward.isDefEq.respectTransparency false in
/-- Simple projections form the dual basis to simple inclusions. -/
theorem pairing_simpleProjection (V : C.Obj) (i : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ V))) :
    simpleHomPairingEquiv C i V (simpleProjection C V i a) =
      (simpleInclusionBasis C V i).dualBasis a := by
  let : Simple (simples C i) := simples_simple C i
  apply (simpleInclusionBasis C V i).ext
  intro b
  rw [Module.Basis.dualBasis_apply_self]
  simp [simpleHomPairingEquiv, simpleHomPairing,
    simpleInclusion, simpleProjection, Category.assoc, biproduct.ι_π]
  split_ifs <;> simp <;> exact End.ext rfl

/-- Basis contractions are natural in an arbitrary morphism. -/
theorem simpleBasis_contraction_natural {V W : C.Obj} (i : Fin (rank C)) (q : V ⟶ W) {E : Type*}
    [AddCommGroup E] [Module ℂ E] (F : (simples C i ⟶ W) →ₗ[ℂ] (V ⟶ simples C i) →ₗ[ℂ] E) :
    (∑ a, F (simpleInclusion C V i a ≫ q) (simpleProjection C V i a)) =
      ∑ b, F (simpleInclusion C W i b) (q ≫ simpleProjection C W i b) := by
  let A := simpleInclusionBasis C V i
  let B := simpleInclusionBasis C W i
  let P := simpleHomPairingEquiv C i V
  let F' : (simples C i ⟶ W) →ₗ[ℂ]
      Module.Dual ℂ (simples C i ⟶ V) →ₗ[ℂ] E :=
    (LinearMap.lcomp ℂ E P.symm.toLinearMap).comp F
  simpa only [F', LinearMap.comp_apply, LinearMap.lcomp_apply, Linear.rightComp_apply,
    LinearEquiv.coe_coe, A, B, P, simpleInclusionBasis_apply,
    ← pairing_simpleProjection, ← simpleHomPairingEquiv_natural, LinearEquiv.symm_apply_apply] using
    dualBasis_contraction_natural A B (Linear.rightComp ℂ (simples C i) q) F'

/-- A mixed crossing block, with the input and output test strands allowed
to differ, is bilinear in its two fusion morphisms. -/
def mixedCrossingBilinear {k : Type*} [CommSemiring k] {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
    [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D] (X T U R S : D) : (R ⟶ U ⊗ S) →ₗ[k]
      (T ⊗ S ⟶ R) →ₗ[k] (((R ⊗ X) ⊗ Rᘁ) ⊗ T ⟶ U ⊗ ((S ⊗ X) ⊗ Sᘁ)) where
  toFun g := {
    toFun := fun f =>
      (α_ (R ⊗ X) (Rᘁ) T).hom ≫ ((g ▷ X) ⊗ₘ closeFusionMap T S f) ≫
        (α_ (U ⊗ S) X (Sᘁ)).hom ≫ (α_ U S (X ⊗ Sᘁ)).hom ≫
          (U ◁ (α_ S X (Sᘁ)).inv)
    map_add' := by
      intro f f'
      simp [closeFusionMap, rightAdjointMate, Category.assoc,
        tensorHom_def, MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
       Preadditive.comp_add, Preadditive.add_comp]
    map_smul' := by
      intro r f
      simp [closeFusionMap, rightAdjointMate, Category.assoc,
        tensorHom_def, MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
       Linear.comp_smul, Linear.smul_comp] }
  map_add' := by
    intro g g'
    ext f
    simp [Category.assoc, tensorHom_def, MonoidalPreadditive.add_whiskerRight,
      Preadditive.comp_add, Preadditive.add_comp]
  map_smul' := by
    intro r g
    ext f
    simp [Category.assoc, tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Linear.comp_smul, Linear.smul_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A finite splitting can be used to refine a simple-basis contraction. -/
theorem simpleBasis_contraction_refinement {J : Type} [Fintype J] {V : J → C.Obj} {W : C.Obj}
    (i : Fin (rank C)) (q : ∀ j, V j ⟶ W) (r : ∀ j, W ⟶ V j)
    (h : (∑ j, r j ≫ q j) = 𝟙 W)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : (simples C i ⟶ W) →ₗ[ℂ] (W ⟶ simples C i) →ₗ[ℂ] E) :
    (∑ j, ∑ a, F (simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection C (V j) i a)) =
      ∑ b, F (simpleInclusion C W i b) (simpleProjection C W i b) := by
  have step (j : J) : (∑ a, F (simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection C (V j) i a)) =
      ∑ b, F (simpleInclusion C W i b) (r j ≫ q j ≫ simpleProjection C W i b) := by
    let F' : (simples C i ⟶ W) →ₗ[ℂ] (V j ⟶ simples C i) →ₗ[ℂ] E :=
      (LinearMap.lcomp ℂ E (Linear.leftComp ℂ (simples C i) (r j))).comp F
    simpa [F', Category.assoc] using simpleBasis_contraction_natural C i (q j) F'
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← map_sum, ← Category.assoc, ← Preadditive.sum_comp, h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Nested fusion decompositions give the direct crossing-block contraction. -/
theorem crossingBlock_refinement (X T U : C.Obj) (i j : Fin (rank C)) :
    (∑ p : simplePieces C (U ⊗ simples C j), ∑ a : crossingIndex C T i p.1,
      nestedCrossingBlock C X T U i p.1 j a p.2) = ∑ b, crossingSummand C X (T ⊗ U) i j b := by
  let J := simplePieces C (U ⊗ simples C j)
  let W := (T ⊗ U) ⊗ simples C j
  let V : J → C.Obj := fun p => T ⊗ simples C p.1
  let q (p : J) : V p ⟶ W := (T ◁ crossingInclusion C U p.1 j p.2) ≫ (α_ T U (simples C j)).inv
  let r (p : J) : W ⟶ V p := (α_ T U (simples C j)).hom ≫ (T ◁ crossingProjection C U p.1 j p.2)
  have h : (∑ p, r p ≫ q p) = 𝟙 W := by
    simp only [r, q, Category.assoc, ← whiskerLeft_comp_assoc,
      ← Preadditive.comp_sum, ← Preadditive.sum_comp, ← whiskerLeft_sum]
    rw [crossing_completeness]
    simp [W]
  simpa [V, W, J, q, r, nestedCrossingBlock, crossingSummand, simpleProjection,
    crossingInclusion, crossingProjection, mixedCrossingBilinear, crossingBlock, Category.assoc] using
    simpleBasis_contraction_refinement C i q r h
      (mixedCrossingBilinear (k := ℂ) X (T ⊗ U) (T ⊗ U) (simples C i) (simples C j))

end PropertyF.Ground.CentreInduction

end

/-! Naturality in the crossed object for the proposed induction crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- Closing a fusion map is natural in its test strand. -/
theorem closeFusionMap_pre_test {T U R S : D} (h : T ⟶ U) (f : U ⊗ S ⟶ R) :
    (Rᘁ ◁ h) ≫ closeFusionMap U S f =
      closeFusionMap T S ((h ▷ S) ≫ f) := by
  simp only [closeFusionMap, Category.assoc, comp_rightAdjointMate, comp_whiskerRight]
  rw [whisker_exchange_assoc]
  have hn := congrArg (fun k => k ▷ T) (rightDualTensorIso_natural h (𝟙 S))
  simp only [tensorHom_id, rightAdjointMate_id, id_tensorHom, comp_whiskerRight] at hn
  rw [reassoc_of% hn]
  rw [whisker_exchange_assoc, associator_naturality_right_assoc]
  rw [associator_naturality_middle_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [rightAdjointMate_comp_evaluation]

variable {k : Type*} [CommSemiring k] [Preadditive D] [Linear k D]
  [MonoidalPreadditive D] [MonoidalLinear k D]

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the output of a crossing block composes the
fusion inclusion with that map. -/
@[reassoc]
theorem crossingBlock_post_test (X : D) {T U R S : D} (h : T ⟶ U)
    (g : R ⟶ T ⊗ S) (f : T ⊗ S ⟶ R) :
    crossingBlock X T S g f ≫ (h ▷ ((S ⊗ X) ⊗ Sᘁ)) =
      mixedCrossingBilinear (k := k) X T U R S (g ≫ (h ▷ S)) f := by
  simp only [crossingBlock, mixedCrossingBilinear, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Moving a test-strand map to the input of a crossing block composes the
fusion projection with that map. -/
@[reassoc]
theorem crossingBlock_pre_test (X : D) {T U R S : D} (h : T ⟶ U)
    (g : R ⟶ U ⊗ S) (f : U ⊗ S ⟶ R) :
    (((R ⊗ X) ⊗ Rᘁ) ◁ h) ≫ crossingBlock X U S g f =
      mixedCrossingBilinear (k := k) X T U R S g ((h ▷ S) ≫ f) := by
  simp only [crossingBlock, mixedCrossingBilinear, LinearMap.coe_mk, AddHom.coe_mk,
    tensorHom_def, Category.assoc]
  rw [associator_naturality_right_assoc, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    closeFusionMap_pre_test, whisker_exchange_assoc]

/-- Summing the crossing blocks removes the dependence on the chosen fusion
basis, so a map of test objects can pass through each matrix entry. -/
theorem crossingBlock_sum_natural_test
    (X T U : C.Obj) (h : T ⟶ U) (i j : Fin (rank C)) :
    (∑ b, (((simples C i ⊗ X) ⊗ (simples C i)ᘁ) ◁ h) ≫ crossingSummand C X U i j b) =
    ∑ a, crossingSummand C X T i j a ≫ (h ▷ ((simples C j ⊗ X) ⊗ (simples C j)ᘁ)) := by
  simpa only [crossingSummand, crossingBlock_pre_test (k := ℂ), crossingBlock_post_test (k := ℂ),
    crossingInclusion, crossingProjection, simpleProjection] using
    (simpleBasis_contraction_natural C i (h ▷ simples C j)
      (mixedCrossingBilinear (k := ℂ) X T U (simples C i) (simples C j))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The proposed induction crossing is natural in the crossed object. -/
theorem crossingCandidate_natural_test
    (X : C.Obj) {T U : C.Obj} (h : T ⟶ U) :
    (underlying C X ◁ h) ≫ crossingCandidate C X U =
      crossingCandidate C X T ≫ (h ▷ underlying C X) := by
  let V := inductionSummand C X
  apply (cancel_epi (rightDistributor V T).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  dsimp [V, underlying] at *
  rw [← whisker_exchange_assoc]
  simp only [crossingCandidate_on_summand, crossingCandidate_on_summand_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Category.assoc, whisker_exchange, Preadditive.sum_comp, V] using
    congrArg (fun g => g ≫ (U ◁ biproduct.ι V j)) (crossingBlock_sum_natural_test C X T U h i j)

end PropertyF.Ground.CentreInduction
