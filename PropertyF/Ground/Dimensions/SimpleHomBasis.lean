module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Dimensions.TensorMultiplicativity
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Dimensions.ENOMatrices
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Traces on simple multiplicity spaces

Partial traces, bases, and composition pairings describe simple multiplicity spaces.

## Main results

* `rightQuantumTrace_tensor_scalar`: expresses tensor quantum traces as products of scalars.
* `simpleInclusion`: constructs inclusion maps for a simple multiplicity space.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- Closing an identity strand gives the right quantum trace as a scalar. -/
theorem partialTraceWith_one {Y : C} (k : Y ≅ (Yᘁ)ᘁ) (X : C) :
    partialTraceWith k X 1 =
      End.of ((ρ_ X).inv ≫ X ◁ (rightQuantumTrace k).asHom ≫ (ρ_ X).hom) := by
  apply End.ext
  simp only [partialTraceWith, rightQuantumTrace, End.one_asHom,
    id_whiskerRight, Category.id_comp, whiskerLeft_comp, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Quantum dimensions multiply for any two double-dual isomorphisms, without
a naturality or pivotal assumption. -/
theorem rightQuantumTrace_tensor_scalar
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) {X Y : C}
    (j : X ≅ (Xᘁ)ᘁ) (k : Y ≅ (Yᘁ)ᘁ) :
    scalar (rightQuantumTrace ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y)) =
      scalar (rightQuantumTrace j) * scalar (rightQuantumTrace k) := by
  have hpt : partialTraceWith k X 1 = scalar (rightQuantumTrace k) • 1 := by
    rw [partialTraceWith_one, eq_smul_one_of_algEquiv scalar (rightQuantumTrace k)]
    apply End.ext
    simp
  have h := rightTraceWith_partialTraceWith j k (1 : End (X ⊗ Y))
  rw [hpt] at h
  have ht : rightQuantumTrace ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) =
      scalar (rightQuantumTrace k) • rightQuantumTrace j := by
    apply End.homEquiv.injective
    simpa [rightTraceWith, rightQuantumTrace, tensorHom_def] using (congrArg End.asHom h.symm)
  rw [ht, map_smul, smul_eq_mul, mul_comm]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- Closing the inverse tensor defect with the natural root gives the product
of the two simple root dimensions. -/
theorem rootTrace_inverseDefect
    (i j : Fin (rank C)) :
    unitScalar C (rootTrace C (rootTensorDefect C (simples C i) (simples C j)).inv) =
      rootDimension C i * rootDimension C j := by
  simpa only [rootDimension, rootTrace_id, Ground.unitScalar_eq_equiv, rootTrace,
    rightTraceWith, rightQuantumTrace, rootTensorDefect, rootTensorIso,
    Iso.trans_inv, Iso.symm_inv, Functor.id_obj, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.id_comp, Category.comp_id] using
      rightQuantumTrace_tensor_scalar (Ground.unitScalarEquiv C)
        ((fourthDualRootNaturalIso C).app (simples C i))
        ((fourthDualRootNaturalIso C).app (simples C j))

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A weighted sum of inclusions projects onto its matching simple summand. -/
theorem simplePieces_sum_projection (X : C.Obj) (k : Fin (rank C))
    (c : Fin (Module.finrank ℂ (simples C k ⟶ X)) → ℂ)
    (t : Fin (Module.finrank ℂ (simples C k ⟶ X))) :
    (∑ x, c x • (biproduct.ι (simplePiecesObject C X) ⟨k, x⟩ ≫
      biproduct.π (simplePiecesObject C X) ⟨k, t⟩)) = c t • 𝟙 (simples C k) := by
  classical
  rw [Finset.sum_eq_single_of_mem t (Finset.mem_univ t) ?_]
  · simp
  · intro x _ hxt
    rw [biproduct.ι_π_ne (simplePiecesObject C X) (by simpa using hxt)]
    exact smul_zero _

set_option backward.isDefEq.respectTransparency false in
theorem simpleInclusion_independent
    (X : C.Obj) (k : Fin (rank C)) :
    LinearIndependent ℂ (simpleInclusion C X k) := by
  classical
  let : Simple (simples C k) := simples_simple C k
  apply Fintype.linearIndependent_iff.mpr
  intro g hg t
  have h := congrArg (fun f : simples C k ⟶ X =>
    f ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩) hg
  simp only [Preadditive.sum_comp, Linear.smul_comp, zero_comp, simpleInclusion,
    Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [simplePieces_sum_projection C X k g t] at h
  exact smul_left_injective ℂ (id_nonzero (simples C k)) (by simpa using h)

/-- The canonical summand inclusions form a basis of each simple Hom space. -/
def simpleInclusionBasis (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (rank C)) :
    Module.Basis (Fin (Module.finrank ℂ (simples C k ⟶ X))) ℂ (simples C k ⟶ X) := by
  letI : FiniteDimensional ℂ (simples C k ⟶ X) := IsFusionCategory.hom_finite _ _
  exact basisOfLinearIndependentOfCardEqFinrank' (simpleInclusion C X k)
    (simpleInclusion_independent C X k) (Fintype.card_fin _)

@[simp]
theorem simpleInclusionBasis_apply
    (X : C.Obj) (k : Fin (rank C))
    (t : Fin (Module.finrank ℂ (simples C k ⟶ X))) :
    simpleInclusionBasis C X k t = simpleInclusion C X k t :=
  letI : FiniteDimensional ℂ (simples C k ⟶ X) := IsFusionCategory.hom_finite _ _
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) t

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates in the simple-inclusion basis are the scalar diagonal
projections of the morphism. -/
theorem simpleInclusionBasis_projection
    {X : C.Obj} {k : Fin (rank C)} (g : simples C k ⟶ X)
    (t : Fin (Module.finrank ℂ (simples C k ⟶ X))) :
    ((simpleInclusionBasis C X k).repr g t) • 𝟙 (simples C k) =
      g ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩ := by
  classical
  let b := simpleInclusionBasis C X k
  have h := congrArg (fun f : simples C k ⟶ X =>
    f ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩) (b.sum_repr g)
  dsimp only [b] at h
  simp only [Preadditive.sum_comp, Linear.smul_comp, simpleInclusionBasis_apply, simpleInclusion,
    Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [simplePieces_sum_projection C X k (b.repr g) t] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary trace on a simple Hom space is the sum of scalar diagonal
blocks in the chosen object decomposition. -/
theorem simpleHom_postcomp_trace
    {X : C.Obj} {k : Fin (rank C)} (g : X ⟶ X)
    (c : Fin (Module.finrank ℂ (simples C k ⟶ X)) → ℂ)
    (hc : ∀ t, biproduct.ι (simplePiecesObject C X) ⟨k, t⟩ ≫
      (simpleDecomposition C X).inv ≫ g ≫ (simpleDecomposition C X).hom ≫
        biproduct.π (simplePiecesObject C X) ⟨k, t⟩ = c t • 𝟙 (simples C k)) :
    LinearMap.trace ℂ _ (Linear.rightComp ℂ (simples C k) g) = ∑ t, c t := by
  classical
  let : Simple (simples C k) := simples_simple C k
  let : FiniteDimensional ℂ (simples C k ⟶ X) := IsFusionCategory.hom_finite _ _
  rw [LinearMap.trace_eq_matrix_trace ℂ (simpleInclusionBasis C X k)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro t _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Linear.rightComp_apply,
    simpleInclusionBasis_apply]
  apply smul_left_injective ℂ (id_nonzero (simples C k))
  simpa [simpleInclusion, Category.assoc, hc t] using
    (simpleInclusionBasis_projection C (simpleInclusion C X k t ≫ g) t)

set_option backward.isDefEq.respectTransparency false in
/-- The natural-root categorical trace equals the dimension-weighted sum of
ordinary traces on the simple Hom spaces. -/
theorem rootTrace_eq_simpleHom_trace_sum
    {X : C.Obj} (g : X ⟶ X) :
    unitScalar C (rootTrace C g) =
      ∑ k, LinearMap.trace ℂ _ (Linear.rightComp ℂ (simples C k) g) * rootDimension C k := by
  classical
  let V := simplePiecesObject C X
  let e := simpleDecomposition C X
  let f : (⨁ V) ⟶ (⨁ V) := e.inv ≫ g ≫ e.hom
  have heq : rootTrace C g = rootTrace C f := by
    simpa [f, Category.assoc] using (rootTrace_cyclic C e.hom (e.inv ≫ g))
  obtain ⟨c, hc, ht⟩ := rootTrace_biproduct_simple C V (fun a => simples_simple C a.1) f
  rw [heq, ht]
  simp only [Ground.unitScalar_eq_equiv, map_sum, map_smul, smul_eq_mul, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  have hblock : ∀ t, biproduct.ι V ⟨k, t⟩ ≫ e.inv ≫ g ≫ e.hom ≫ biproduct.π V ⟨k, t⟩ =
      c ⟨k, t⟩ • 𝟙 (simples C k) := by
    intro t
    simpa [f, Category.assoc] using hc ⟨k, t⟩
  rw [(simpleHom_postcomp_trace C g (fun t => c ⟨k,t⟩) hblock), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  change c ⟨k, t⟩ * (Ground.unitScalarEquiv C (rootTrace C (𝟙 (simples C k)))) =
    c ⟨k, t⟩ * rootDimension C k
  rw [← Ground.unitScalar_eq_equiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Involutivity of every multiplicity operator implies ENO's trace-matrix
root-dimension eigenvector identity. -/
theorem enoTraceMatrix_eigenvector_of_involutions {i j : Fin (rank C)}
    (hinv : ∀ k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    ∑ k, enoTraceMatrix C i j k * rootDimension C k = rootDimension C i * rootDimension C j := by
  let d := rootTensorDefect C (simples C i) (simples C j)
  have hop (k : Fin (rank C)) :
      Linear.rightComp ℂ (simples C k) d.inv = (multiplicityDefect C i j k).toLinearMap := by
    ext f
    have hs : (multiplicityDefect C i j k).symm f = multiplicityDefect C i j k f :=
      (LinearEquiv.symm_apply_eq _).2 (congrArg (fun L => L f) (hinv k)).symm
    simpa [multiplicityDefect, Linear.homCongr_apply, Linear.homCongr_symm_apply, d] using hs
  have ht := rootTrace_eq_simpleHom_trace_sum C d.inv
  rw [rootTrace_inverseDefect] at ht
  simpa only [enoTraceMatrix, hop] using ht.symm

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Composition induces the scalar-valued pairing between morphisms to and
from a simple object. -/
def simpleHomPairing (C : BraidedFusionCategory.{v,u})
    (S X : C.Obj) [Simple S] : (X ⟶ S) →ₗ[ℂ] Module.Dual ℂ (S ⟶ X) := by
  letI : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  exact {
    toFun g := {
      toFun := fun f => Ground.simpleEndScalar S (End.of (f ≫ g))
      map_add' := by
        intro f f'
        simp only [Preadditive.add_comp]
        change Ground.simpleEndScalar S (End.of (f ≫ g) + End.of (f' ≫ g)) = _
        exact map_add _ _ _
      map_smul' := by
        intro z f
        simp only [Linear.smul_comp]
        change Ground.simpleEndScalar S (z • End.of (f ≫ g)) = z • _
        exact map_smul _ _ _ }
    map_add' := by
      intro g g'
      ext f
      simp only [Preadditive.comp_add]
      change Ground.simpleEndScalar S (End.of (f ≫ g) + End.of (f ≫ g')) = _
      exact map_add _ _ _
    map_smul' := by
      intro z g
      ext f
      simp only [Linear.comp_smul]
      change Ground.simpleEndScalar S (z • End.of (f ≫ g)) = z • _
      exact map_smul _ _ _
  }

set_option backward.isDefEq.respectTransparency false in
/-- The composition pairing is nondegenerate in the morphism-to-simple factor. -/
theorem simpleHomPairing_injective
    (S X : C.Obj) [Simple S] : Function.Injective (simpleHomPairing C S X) := by
  let : FiniteDimensional ℂ (S ⟶ S) := IsFusionCategory.hom_finite _ _
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro g hg
  by_contra hne
  obtain ⟨f, hf⟩ := Ground.split_to_simple C g hne
  have h := congrArg (fun F : Module.Dual ℂ (S ⟶ X) => F f) hg
  change Ground.simpleEndScalar S (End.of (f ≫ g)) = 0 at h
  rw [hf] at h
  change Ground.simpleEndScalar S 1 = 0 at h
  simp at h

/-- The composition pairing is perfect for each representative simple. -/
def simpleHomPairingEquiv (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) (X : C.Obj) :
    (X ⟶ simples C i) ≃ₗ[ℂ] Module.Dual ℂ (simples C i ⟶ X) := by
  letI : Simple (simples C i) := simples_simple C i
  letI : FiniteDimensional ℂ (X ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  letI : FiniteDimensional ℂ (simples C i ⟶ X) := IsFusionCategory.hom_finite _ _
  let p := simpleHomPairing C (simples C i) X
  have hi := simpleHomPairing_injective C (simples C i) X
  have hd : Module.finrank ℂ (X ⟶ simples C i) =
      Module.finrank ℂ (Module.Dual ℂ (simples C i ⟶ X)) :=
    (finrank_to_simple_eq_from_simple C X i).trans
      (Subspace.dual_finrank_eq (K := ℂ) (V := simples C i ⟶ X)).symm
  exact LinearEquiv.ofBijective p ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hi⟩

/-- Composition pairs precomposition on one Hom space with postcomposition on
the other. -/
theorem simpleHomPairing_natural
    {S X : C.Obj} [Simple S] (g : X ⟶ S) (a : X ⟶ X) :
    simpleHomPairing C S X (a ≫ g) =
      Module.Dual.transpose (Linear.rightComp ℂ S a) (simpleHomPairing C S X g) := by
  ext f
  simp [simpleHomPairing, Module.Dual.transpose_apply, Linear.rightComp_apply, Category.assoc]

end PropertyF.Ground.Dimensions
