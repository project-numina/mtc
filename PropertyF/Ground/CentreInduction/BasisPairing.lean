module
public import PropertyF.Ground.CentreInduction.CrossingBlocks
public import PropertyF.Ground.Dimensions.SimplePairing
public import Mathlib.LinearAlgebra.Dual.Basis

/-! Dual bases for the actual fusion summand inclusions and projections. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- A projection from a chosen fusion decomposition corresponds to the dual
basis functional of the matching inclusion. -/
theorem pairing_crossingProjection
    (T : C.Obj) (i j : Fin (rank C))
    (a : Fin (Module.finrank ℂ (simples C i ⟶ T ⊗ simples C j))) :
    Dimensions.simpleHomPairingEquiv C i (T ⊗ simples C j) (crossingProjection C T i j a) =
      (Dimensions.simpleInclusionBasis C (T ⊗ simples C j) i).dualBasis a := by
  classical
  let : Simple (simples C i) := simples_simple C i
  let B := Dimensions.simpleInclusionBasis C (T ⊗ simples C j) i
  apply B.ext
  intro b
  rw [Module.Basis.dualBasis_apply_self]
  by_cases hab : b = a
  · subst b
    have hh : Dimensions.simpleInclusion C (T ⊗ simples C j) i a ≫
        crossingProjection C T i j a = 𝟙 _ := crossingInclusion_projection C T i j a
    simp [Dimensions.simpleHomPairingEquiv, Dimensions.simpleHomPairing, B, hh]
    apply End.ext
    rfl
  · have hz := crossingInclusion_projection_ne C T j
      (⟨i, b⟩ : Σ k, Fin (Module.finrank ℂ (simples C k ⟶ T ⊗ simples C j)))
      ⟨i, a⟩ (by simpa using hab)
    change Dimensions.simpleInclusion C (T ⊗ simples C j) i b ≫
      crossingProjection C T i j a = 0 at hz
    simp [Dimensions.simpleHomPairingEquiv, Dimensions.simpleHomPairing, B, hz, hab]
    apply End.ext
    rfl

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

/-- The fusion-basis contraction is independent of which side of a map
`T ⊗ Sⱼ ⟶ U ⊗ Sⱼ` is used to insert the decomposition. -/
theorem fusionBasis_contraction_natural
    {T U : C.Obj} (i j : Fin (rank C))
    (q : T ⊗ simples C j ⟶ U ⊗ simples C j)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : (simples C i ⟶ U ⊗ simples C j) →ₗ[ℂ]
      (T ⊗ simples C j ⟶ simples C i) →ₗ[ℂ] E) :
    (∑ a, F (crossingInclusion C T i j a ≫ q) (crossingProjection C T i j a)) =
      ∑ b, F (crossingInclusion C U i j b) (q ≫ crossingProjection C U i j b) := by
  classical
  let A := Dimensions.simpleInclusionBasis C (T ⊗ simples C j) i
  let B := Dimensions.simpleInclusionBasis C (U ⊗ simples C j) i
  let P := Dimensions.simpleHomPairingEquiv C i (T ⊗ simples C j)
  let F' : (simples C i ⟶ U ⊗ simples C j) →ₗ[ℂ]
      Module.Dual ℂ (simples C i ⟶ T ⊗ simples C j) →ₗ[ℂ] E :=
    { toFun := fun g => (F g).comp P.symm.toLinearMap
      map_add' := by intro x y; ext z; simp
      map_smul' := by intro r x; ext z; simp }
  have h := dualBasis_contraction_natural A B (Linear.rightComp ℂ (simples C i) q) F'
  have hproj (a) : P.symm (A.dualBasis a) = crossingProjection C T i j a := by
    apply P.injective
    simpa [P, A] using (pairing_crossingProjection C T i j a).symm
  have hdual (b) : P.symm (Module.Dual.transpose (Linear.rightComp ℂ (simples C i) q)
      (B.dualBasis b)) = q ≫ crossingProjection C U i j b := by
    apply P.injective
    rw [P.apply_symm_apply]
    symm
    rw [simpleHomPairingEquiv_natural, pairing_crossingProjection]
  change (∑ a, F (A a ≫ q) (P.symm (A.dualBasis a))) =
    ∑ b, F (B b) (P.symm (Module.Dual.transpose
      (Linear.rightComp ℂ (simples C i) q) (B.dualBasis b))) at h
  simp_rw [hproj, hdual] at h
  simpa only [A, B, Dimensions.simpleInclusionBasis_apply, crossingInclusion] using h

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

end PropertyF.Ground.CentreInduction
