module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dual.Basis
public import MTC.Fusion.SemisimpleSplit
public import MTC.CategoryTheory.Dimensions.TensorMultiplicativity
public import MTC.CategoryTheory.Dimensions.SquaredNorm
public import MTC.CategoryTheory.Dimensions.ENOMatrices
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Traces on simple multiplicity spaces

Partial traces, bases, and composition pairings describe simple multiplicity spaces.

## Main results

* `rightQuantumTrace_tensor_scalar`: expresses tensor quantum traces as products of scalars.
* `simpleInclusion`: constructs inclusion maps for a simple multiplicity space.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
variable {R : Type*} [CommSemiring R] [Preadditive C] [Linear R C]
  [MonoidalPreadditive C] [MonoidalLinear R C]
set_option backward.isDefEq.respectTransparency false in
/-- Quantum dimensions multiply for any two double-dual isomorphisms, without
a naturality or pivotal assumption. -/
theorem rightQuantumTrace_tensor_scalar (scalar : End (𝟙_ C) ≃ₐ[R] R) {X Y : C}
    (j : X ≅ (Xᘁ)ᘁ) (k : Y ≅ (Yᘁ)ᘁ) :
    scalar (rightQuantumTrace ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y)) =
      scalar (rightQuantumTrace j) * scalar (rightQuantumTrace k) := by
  have hpt : partialTraceWith k X 1 = scalar (rightQuantumTrace k) • 1 := by
    simpa only [id_tensorHom_id, show End.of (𝟙 (X ⊗ Y)) = (1 : End (X ⊗ Y)) from rfl,
      rightTraceWith_id] using partialTraceWith_tensor_right_scalar scalar k X (𝟙 Y)
  simpa only [map_smul, smul_eq_mul, mul_comm] using congrArg scalar
    (show rightQuantumTrace ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) =
        scalar (rightQuantumTrace k) • rightQuantumTrace j from by
      apply End.homEquiv.injective
      simpa [hpt, rightTraceWith, rightQuantumTrace, tensorHom_def] using
        congrArg End.asHom (rightTraceWith_partialTraceWith j k (1 : End (X ⊗ Y))).symm)

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Closing the inverse tensor defect with the natural root gives the product
of the two simple root dimensions. -/
theorem rootTrace_inverseDefect (i j : Fin (rank C)) :
    unitScalar C (rootTrace C (rootTensorDefect C (simples C i) (simples C j)).inv) =
      rootDimension C i * rootDimension C j := by
  simpa only [rootDimension, rootTrace_id, MTC.unitScalar_eq_equiv, rootTrace,
    rightTraceWith, rightQuantumTrace, rootTensorDefect, rootTensorIso,
    Iso.trans_inv, Iso.symm_inv, Functor.id_obj, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.id_comp, Category.comp_id] using
      rightQuantumTrace_tensor_scalar (MTC.unitScalarEquiv C)
        ((fourthDualRootNaturalIso C).app (simples C i))
        ((fourthDualRootNaturalIso C).app (simples C j))

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.CategoryTheory.Dimensions
universe v u

section
variable {k : Type*} [CommSemiring k] {I J : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
variable {A B F : Type*} [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
  [AddCommMonoid F] [Module k F]

/-- A bilinear contraction with dual bases is natural under any linear map.
This is the matrix identity needed to change fusion bases across a morphism. -/
theorem dualBasis_contraction_natural (a : Module.Basis I k A) (b : Module.Basis J k B)
    (L : A →ₗ[k] B) (f : B →ₗ[k] Module.Dual k A →ₗ[k] F) :
    (∑ i, f (L (a i)) (a.dualBasis i)) =
      ∑ j, f (b j) (Module.Dual.transpose L (b.dualBasis j)) := by
  let c : I → J → k := fun i j => b.repr (L (a i)) j
  have hL (i : I) : L (a i) = ∑ j, c i j • b j := (b.sum_repr _).symm
  have hD (j : J) : Module.Dual.transpose L (b.dualBasis j) =
      ∑ i, c i j • a.dualBasis i := by
    simpa [c, Module.Basis.dualBasis_repr, Module.Dual.transpose_apply] using
      (a.dualBasis.sum_repr (Module.Dual.transpose L (b.dualBasis j))).symm
  simp only [hL, hD, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm
end

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts IsFusionCategory.hom_finite
local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i

set_option backward.isDefEq.respectTransparency false in
theorem simpleInclusion_independent
    (X : C.Obj) (k : Fin (rank C)) :
    LinearIndependent ℂ (simpleInclusion C X k) :=
  Fintype.linearIndependent_iff.mpr fun g hg t ↦
    smul_left_injective ℂ (id_nonzero (simples C k)) (by
      simpa [simpleInclusion, Category.assoc, Preadditive.sum_comp, Linear.smul_comp,
        biproduct.ι_π] using congrArg (fun f : simples C k ⟶ X ↦
          f ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩) hg)

/-- The canonical summand inclusions form a basis of each simple Hom space. -/
def simpleInclusionBasis (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (rank C)) :
    Module.Basis (Fin (simpleMultiplicity C k X)) ℂ (simples C k ⟶ X) :=
  basisOfLinearIndependentOfCardEqFinrank' (simpleInclusion C X k)
    (simpleInclusion_independent C X k) (Fintype.card_fin _)

@[simp]
theorem simpleInclusionBasis_apply
    (X : C.Obj) (k : Fin (rank C))
    (t : Fin (simpleMultiplicity C k X)) :
    simpleInclusionBasis C X k t = simpleInclusion C X k t :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) t

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Coordinates in the simple-inclusion basis are the scalar diagonal
projections of the morphism. -/
theorem simpleInclusionBasis_projection {X : C.Obj} {k : Fin (rank C)} (g : simples C k ⟶ X)
    (t : Fin (simpleMultiplicity C k X)) :
    ((simpleInclusionBasis C X k).repr g t) • 𝟙 (simples C k) =
      g ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩ := by
  conv_rhs => rw [← (simpleInclusionBasis C X k).sum_repr g]
  simp [Preadditive.sum_comp, Linear.smul_comp, simpleInclusion, Category.assoc, biproduct.ι_π]

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Ordinary trace on a simple Hom space is the sum of scalar diagonal
blocks in the chosen object decomposition. -/
theorem simpleHom_postcomp_trace {X : C.Obj} {k : Fin (rank C)} (g : X ⟶ X)
    (c : Fin (simpleMultiplicity C k X) → ℂ)
    (hc : ∀ t, biproduct.ι (simplePiecesObject C X) ⟨k, t⟩ ≫
      (simpleDecomposition C X).inv ≫ g ≫ (simpleDecomposition C X).hom ≫
        biproduct.π (simplePiecesObject C X) ⟨k, t⟩ = c t • 𝟙 (simples C k)) :
    LinearMap.trace ℂ _ (Linear.rightComp ℂ (simples C k) g) = ∑ t, c t :=
  (LinearMap.trace_eq_matrix_trace ℂ (simpleInclusionBasis C X k)
    (Linear.rightComp ℂ (simples C k) g)).trans <|
    Finset.sum_congr rfl fun t _ ↦ smul_left_injective ℂ (id_nonzero (simples C k)) (by
      simpa [Matrix.diag_apply, LinearMap.toMatrix_apply, Linear.rightComp_apply,
        simpleInclusion, Category.assoc, hc t] using
          simpleInclusionBasis_projection (simpleInclusion C X k t ≫ g) t)

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The natural-root categorical trace equals the dimension-weighted sum of
ordinary traces on the simple Hom spaces. -/
theorem rootTrace_eq_simpleHom_trace_sum
    {X : C.Obj} (g : X ⟶ X) :
    unitScalar C (rootTrace C g) =
      ∑ k, LinearMap.trace ℂ _ (Linear.rightComp ℂ (simples C k) g) * rootDimension C k := by
  let V := simplePiecesObject C X
  let e := simpleDecomposition C X
  let f : (⨁ V) ⟶ (⨁ V) := e.inv ≫ g ≫ e.hom
  have heq : rootTrace C g = rootTrace C f := by
    simpa [f, Category.assoc] using (rootTrace_cyclic C e.hom (e.inv ≫ g))
  obtain ⟨c, hc, ht⟩ := rootTrace_biproduct_simple V (fun a => simples_simple C a.1) f
  simp only [heq, ht, MTC.unitScalar_eq_equiv, map_sum, map_smul, smul_eq_mul, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [simpleHom_postcomp_trace g (fun t ↦ c ⟨k, t⟩)
    (fun t ↦ by simpa [f, Category.assoc] using hc ⟨k, t⟩), Finset.sum_mul,
    rootDimension, MTC.unitScalar_eq_equiv, V, simplePiecesObject]

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Involutivity of every multiplicity operator implies ENO's trace-matrix
root-dimension eigenvector identity. -/
theorem enoTraceMatrix_eigenvector_of_involutions {i j : Fin (rank C)}
    (hinv : ∀ k, IsInvolutiveElem (multiplicityDefect C i j k).toLinearMap) :
    ∑ k, enoTraceMatrix C i j k * rootDimension C k = rootDimension C i * rootDimension C j :=
  let d := rootTensorDefect C (simples C i) (simples C j)
  have hop (k : Fin (rank C)) :
      Linear.rightComp ℂ (simples C k) d.inv = (multiplicityDefect C i j k).toLinearMap :=
    LinearMap.ext fun f ↦ by
      simpa [multiplicityDefect, Linear.homCongr_apply, Linear.homCongr_symm_apply, d] using
        ((LinearEquiv.symm_apply_eq _).2 (congrArg (fun L ↦ L f) (hinv k)).symm :
          (multiplicityDefect C i j k).symm f = multiplicityDefect C i j k f)
  by simpa only [enoTraceMatrix, hop, d, rootTrace_inverseDefect] using
    (rootTrace_eq_simpleHom_trace_sum d.inv).symm

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.CategoryTheory.Dimensions
universe v u

section
variable {k : Type*} [Field k] [IsAlgClosed k]
  {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D] [HasKernels D]

/-- Composition induces the scalar-valued pairing between morphisms to and
from a simple object. -/
def simpleHomPairing (S X : D) [Simple S] [FiniteDimensional k (S ⟶ S)] :
    (X ⟶ S) →ₗ[k] Module.Dual k (S ⟶ X) :=
  (LinearMap.compRight k ((MTC.simpleEndScalar (k := k) S).toLinearMap.comp
    (End.linearEquiv (R := k) (X := S)).symm.toLinearMap)).comp (Linear.comp S X S).flip


set_option backward.isDefEq.respectTransparency false in
/-- The composition pairing is nondegenerate when every nonzero map to the simple splits. -/
theorem simpleHomPairing_injective
    (S X : D) [Simple S] [FiniteDimensional k (S ⟶ S)]
    (hsplit : ∀ (g : X ⟶ S), g ≠ 0 → ∃ f : S ⟶ X, f ≫ g = 𝟙 S) :
    Function.Injective (simpleHomPairing (k := k) S X) :=
  LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun g hg ↦ by
    by_contra hne
    obtain ⟨f, hf⟩ := hsplit g hne
    have h := congrArg (fun F : Module.Dual k (S ⟶ X) => F f) hg
    change MTC.simpleEndScalar (k := k) S (End.of (f ≫ g)) = 0 at h
    simp only [hf, show End.of (𝟙 S) = (1 : End S) from rfl, map_one, one_ne_zero] at h)

end

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts IsFusionCategory.hom_finite

/-- The composition pairing is perfect for a simple object. -/
def simpleHomPairingEquiv {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] [Abelian D] [Linear ℂ D] [RigidCategory D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] [IsFusionCategory D]
    (S X : D) [Simple S] : (X ⟶ S) ≃ₗ[ℂ] Module.Dual ℂ (S ⟶ X) := by
  let p := simpleHomPairing (k := ℂ) S X
  have hi := simpleHomPairing_injective (k := ℂ) S X fun g hg ↦ MTC.split_to_simple g hg
  have hd : Module.finrank ℂ (X ⟶ S) = Module.finrank ℂ (Module.Dual ℂ (S ⟶ X)) :=
    (finrank_to_simple_eq_from_simple X S).trans
      (Subspace.dual_finrank_eq (K := ℂ) (V := S ⟶ X)).symm
  exact LinearEquiv.ofBijective p ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hi⟩


variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Abelian D] [Linear ℂ D] [RigidCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [IsFusionCategory D]

/-- The perfect pairing commutes with precomposition. -/
theorem simpleHomPairingEquiv_natural {S X Y : D} [Simple S] (g : Y ⟶ S) (a : X ⟶ Y) :
    simpleHomPairingEquiv S X (a ≫ g) =
      Module.Dual.transpose (Linear.rightComp ℂ S a) (simpleHomPairingEquiv S Y g) :=
  LinearMap.ext fun f ↦ by
    simp [simpleHomPairingEquiv, simpleHomPairing, Module.Dual.transpose_apply,
      Linear.rightComp_apply, Category.assoc]


end MTC.CategoryTheory.Dimensions
