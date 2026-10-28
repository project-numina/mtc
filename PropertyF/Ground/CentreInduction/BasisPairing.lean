module
public import PropertyF.Ground.CentreInduction.CrossingBlocks
public import PropertyF.Ground.Dimensions.SimpleHomBasis
public import Mathlib.LinearAlgebra.Dual.Basis

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
theorem simpleHomPairingEquiv_natural
    (i : Fin (rank C)) {V W : C.Obj} (q : V ⟶ W) (f : W ⟶ simples C i) :
    Dimensions.simpleHomPairingEquiv C i V (q ≫ f) =
      Module.Dual.transpose (Linear.rightComp ℂ (simples C i) q)
        (Dimensions.simpleHomPairingEquiv C i W f) := by
  ext g
  simp [Dimensions.simpleHomPairingEquiv, Dimensions.simpleHomPairing,
    Module.Dual.transpose_apply, Linear.rightComp_apply, Category.assoc]

/-- A bilinear contraction with dual bases is natural under any linear map.
This is the matrix identity needed to change fusion bases across a morphism. -/
theorem dualBasis_contraction_natural {k : Type*} [CommSemiring k] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {A B E : Type*} [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    [AddCommMonoid E] [Module k E] (a : Module.Basis I k A) (b : Module.Basis J k B)
    (L : A →ₗ[k] B) (F : B →ₗ[k] Module.Dual k A →ₗ[k] E) :
    (∑ i, F (L (a i)) (a.dualBasis i)) =
      ∑ j, F (b j) (Module.Dual.transpose L (b.dualBasis j)) := by
  classical
  let c : I → J → k := fun i j => b.repr (L (a i)) j
  have hL (i : I) : L (a i) = ∑ j, c i j • b j := (b.sum_repr _).symm
  have hD (j : J) : Module.Dual.transpose L (b.dualBasis j) =
      ∑ i, c i j • a.dualBasis i := by
    calc
      _ = ∑ i, (a.dualBasis.repr (Module.Dual.transpose L (b.dualBasis j)) i) •
        a.dualBasis i := (a.dualBasis.sum_repr _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp [c, Module.Basis.dualBasis_repr,
          Module.Dual.transpose_apply]
  calc
    _ = ∑ i, ∑ j, c i j • F (b j) (a.dualBasis i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hL i]
      simp
    _ = ∑ j, ∑ i, c i j • F (b j) (a.dualBasis i) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hD j]
      simp

set_option backward.isDefEq.respectTransparency false in
/-- Simple projections form the dual basis to simple inclusions. -/
theorem pairing_simpleProjection (V : C.Obj) (i : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ V))) :
    Dimensions.simpleHomPairingEquiv C i V (simpleProjection C V i a) =
      (Dimensions.simpleInclusionBasis C V i).dualBasis a := by
  classical
  let : Simple (simples C i) := simples_simple C i
  let B := Dimensions.simpleInclusionBasis C V i
  apply B.ext
  intro b
  rw [Module.Basis.dualBasis_apply_self]
  by_cases hab : b = a
  · subst b
    simp [Dimensions.simpleHomPairingEquiv, Dimensions.simpleHomPairing, B,
      Dimensions.simpleInclusion, simpleProjection, Category.assoc]
    exact End.ext rfl
  · simp [Dimensions.simpleHomPairingEquiv, Dimensions.simpleHomPairing, B,
      Dimensions.simpleInclusion, simpleProjection, Category.assoc,
      biproduct.ι_π_ne _ (show (⟨i,b⟩ : Dimensions.simplePieces C V) ≠ ⟨i,a⟩ by simpa using hab), hab]
    exact End.ext rfl

/-- Basis contractions are natural in an arbitrary morphism. -/
theorem simpleBasis_contraction_natural {V W : C.Obj} (i : Fin (rank C)) (q : V ⟶ W)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : (simples C i ⟶ W) →ₗ[ℂ] (V ⟶ simples C i) →ₗ[ℂ] E) :
    (∑ a, F (Dimensions.simpleInclusion C V i a ≫ q) (simpleProjection C V i a)) =
      ∑ b, F (Dimensions.simpleInclusion C W i b) (q ≫ simpleProjection C W i b) := by
  classical
  let A := Dimensions.simpleInclusionBasis C V i
  let B := Dimensions.simpleInclusionBasis C W i
  let P := Dimensions.simpleHomPairingEquiv C i V
  let F' : (simples C i ⟶ W) →ₗ[ℂ]
      Module.Dual ℂ (simples C i ⟶ V) →ₗ[ℂ] E :=
    (LinearMap.lcomp ℂ E P.symm.toLinearMap).comp F
  have hproj (a) : P.symm (A.dualBasis a) = simpleProjection C V i a := by
    apply P.injective
    simpa [P, A] using (pairing_simpleProjection C V i a).symm
  have hdual (b) : P.symm (Module.Dual.transpose (Linear.rightComp ℂ (simples C i) q)
      (B.dualBasis b)) = q ≫ simpleProjection C W i b := by
    apply P.injective
    rw [P.apply_symm_apply]
    symm
    rw [simpleHomPairingEquiv_natural, pairing_simpleProjection]
  have h := dualBasis_contraction_natural A B (Linear.rightComp ℂ (simples C i) q) F'
  simp only [F', LinearMap.comp_apply, LinearMap.lcomp_apply, Linear.rightComp_apply, LinearEquiv.coe_coe] at h
  simp_rw [hproj, hdual] at h
  simpa only [A, B, Dimensions.simpleInclusionBasis_apply] using h

/-- A mixed crossing block, with the input and output test strands allowed
to differ, is bilinear in its two fusion morphisms. -/
def mixedCrossingBilinear {k : Type*} [CommSemiring k] {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
    [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D] (X T U R S : D) : (R ⟶ U ⊗ S) →ₗ[k]
      (T ⊗ S ⟶ R) →ₗ[k] (((R ⊗ X) ⊗ Rᘁ) ⊗ T ⟶ U ⊗ ((S ⊗ X) ⊗ Sᘁ)) where
  toFun g := {
    toFun := fun f =>
      (α_ (R ⊗ X) (Rᘁ) T).hom ≫ ((g ▷ X) ⊗ₘ closeFusionMap T S R f) ≫
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
    (∑ j, ∑ a, F (Dimensions.simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection C (V j) i a)) =
      ∑ b, F (Dimensions.simpleInclusion C W i b) (simpleProjection C W i b) := by
  classical
  have step (j : J) : (∑ a, F (Dimensions.simpleInclusion C (V j) i a ≫ q j)
        (r j ≫ simpleProjection C (V j) i a)) =
      ∑ b, F (Dimensions.simpleInclusion C W i b) (r j ≫ q j ≫ simpleProjection C W i b) := by
    let F' : (simples C i ⟶ W) →ₗ[ℂ] (V j ⟶ simples C i) →ₗ[ℂ] E :=
      (LinearMap.lcomp ℂ E (Linear.leftComp ℂ (simples C i) (r j))).comp F
    simpa [F', Category.assoc] using simpleBasis_contraction_natural C i (q j) F'
  simp_rw [step]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← map_sum]
  simp only [← Category.assoc, ← Preadditive.sum_comp, h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Nested fusion decompositions give the direct crossing-block contraction. -/
theorem crossingBlock_refinement (X T U : C.Obj) (i j : Fin (rank C)) :
    (∑ p : Dimensions.simplePieces C (U ⊗ simples C j),
      ∑ a : crossingIndex C T i p.1,
        nestedCrossingBlock C X T U i p.1 j a p.2) =
      ∑ b, crossingSummand C X (T ⊗ U) i j b := by
  classical
  let J := Dimensions.simplePieces C (U ⊗ simples C j)
  let W := (T ⊗ U) ⊗ simples C j
  let V : J → C.Obj := fun p => T ⊗ simples C p.1
  let q (p : J) : V p ⟶ W := (T ◁ crossingInclusion C U p.1 j p.2) ≫ (α_ T U (simples C j)).inv
  let r (p : J) : W ⟶ V p := (α_ T U (simples C j)).hom ≫ (T ◁ crossingProjection C U p.1 j p.2)
  have h : (∑ p, r p ≫ q p) = 𝟙 W := by
    calc
      _ = (α_ T U (simples C j)).hom ≫
        (T ◁ (∑ p : J, crossingProjection C U p.1 j p.2 ≫ crossingInclusion C U p.1 j p.2)) ≫
        (α_ T U (simples C j)).inv := by
          simp only [r, q, whiskerLeft_sum, Preadditive.comp_sum,
            Preadditive.sum_comp, whiskerLeft_comp, Category.assoc]
      _ = _ := by rw [crossing_completeness]; simp [W]
  have hc := simpleBasis_contraction_refinement C i q r h
    (mixedCrossingBilinear (k := ℂ) X (T ⊗ U) (T ⊗ U) (simples C i) (simples C j))
  simpa [V, W, J, q, r, nestedCrossingBlock, crossingSummand, simpleProjection,
    crossingInclusion, crossingProjection, mixedCrossingBilinear, crossingBlock, Category.assoc] using hc

end PropertyF.Ground.CentreInduction
