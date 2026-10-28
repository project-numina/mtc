module
public import PropertyF.Ground.Dimensions.TensorMultiplicativity
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Dimensions.ENOMatrices
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Traces on simple multiplicity spaces

Partial traces and bases of simple multiplicity spaces describe tensor traces and matrix coefficients.
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
  have hscalar : rightQuantumTrace k = scalar (rightQuantumTrace k) • (1 : End (𝟙_ C)) := by
    apply scalar.injective
    simp
  have hpt : partialTraceWith k X 1 = scalar (rightQuantumTrace k) • 1 := by
    rw [partialTraceWith_one, hscalar]
    apply End.ext
    simp
  have h := rightTraceWith_partialTraceWith j k (1 : End (X ⊗ Y))
  rw [hpt] at h
  have ht : rightQuantumTrace ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) =
      scalar (rightQuantumTrace k) • rightQuantumTrace j := by
    apply End.homEquiv.injective
    simpa [rightTraceWith, rightQuantumTrace, tensorHom_def] using (congrArg End.asHom h.symm)
  rw [ht, map_smul]
  simp [mul_comm]

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
    Ground.unitScalar C (rootTrace C (rootTensorDefect C (simples C i) (simples C j)).inv) =
      rootDimension C i * rootDimension C j := by
  let X := simples C i
  let Y := simples C j
  let a := fourthDualRootNaturalIso C
  let b := rootTensorIso C X Y
  let d := rootTensorDefect C X Y
  have hd : d.inv ≫ (a.app (X ⊗ Y)).hom = b.hom := by
    simp [d, rootTensorDefect, b, a, Category.assoc]
  have ht : rootTrace C d.inv = rightQuantumTrace b := by
    apply End.homEquiv.injective
    change η_ (X ⊗ Y) ((X ⊗ Y)ᘁ) ≫
      ((d.inv ≫ (a.app (X ⊗ Y)).hom) ⊗ₘ 𝟙 ((X ⊗ Y)ᘁ)) ≫
        ε_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ) =
      η_ (X ⊗ Y) ((X ⊗ Y)ᘁ) ≫ (b.hom ⊗ₘ 𝟙 ((X ⊗ Y)ᘁ)) ≫
        ε_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ)
    rw [hd]
  rw [ht]
  change Ground.unitScalar C (rightQuantumTrace
    (((a.app X) ⊗ᵢ (a.app Y)) ≪≫ doubleDualTensorIso X Y)) = _
  rw [← groundUnitScalarEquiv_apply]
  let ax : X ≅ (Xᘁ)ᘁ := (a.app X)
  let ay : Y ≅ (Yᘁ)ᘁ := (a.app Y)
  have hp := rightQuantumTrace_tensor_scalar (groundUnitScalarEquiv C) ax ay
  change (groundUnitScalarEquiv C) (rightQuantumTrace ((ax ⊗ᵢ ay) ≪≫ doubleDualTensorIso X Y)) =
    rootDimension C i * rootDimension C j
  rw [hp]
  have hx : groundUnitScalarEquiv C (rightQuantumTrace ax) = rootDimension C i := by
    simp [rootDimension, rootTrace, rightTraceWith, rightQuantumTrace, groundUnitScalarEquiv_apply, X, a, ax]
  have hy : groundUnitScalarEquiv C (rightQuantumTrace ay) = rootDimension C j := by
    simp [rootDimension, rootTrace, rightTraceWith, rightQuantumTrace, groundUnitScalarEquiv_apply, Y, a, ay]
  rw [hx, hy]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The inclusion of a chosen simple summand in the canonical decomposition. -/
def simpleInclusion (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
    (k : Fin (rank C)) (t : Fin (Module.finrank ℂ (simples C k ⟶ X))) :
    simples C k ⟶ X :=
  biproduct.ι (simplePiecesObject C X) ⟨k, t⟩ ≫ (simpleDecomposition C X).inv

set_option backward.isDefEq.respectTransparency false in
theorem simpleInclusion_independent
    (X : C.Obj) (k : Fin (rank C)) :
    LinearIndependent ℂ (simpleInclusion C X k) := by
  classical
  let : Simple (simples C k) := Ground.simples_simple C k
  apply Fintype.linearIndependent_iff.mpr
  intro g hg t
  have h := congrArg (fun f : simples C k ⟶ X =>
    f ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩) hg
  simp only [Preadditive.sum_comp, Linear.smul_comp, zero_comp] at h
  have hh : g t • 𝟙 (simples C k) = 0 := by
    simp [simpleInclusion, Category.assoc] at h
    have he : (∑ x, g x • (biproduct.ι (simplePiecesObject C X) ⟨k, x⟩ ≫
        biproduct.π (simplePiecesObject C X) ⟨k, t⟩)) = g t • 𝟙 (simples C k) := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro x _ hxt
        rw [biproduct.ι_π_ne (simplePiecesObject C X) (by simpa using hxt)]
        simp
      · simp
    rw [he] at h
    exact h
  have := (smul_left_injective ℂ (id_nonzero (simples C k))) (by simpa using hh : g t • 𝟙 _ = (0 : ℂ) • 𝟙 _)
  exact this

/-- The canonical summand inclusions form a basis of each simple Hom space. -/
def simpleInclusionBasis (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (rank C)) :
    Module.Basis (Fin (Module.finrank ℂ (simples C k ⟶ X))) ℂ (simples C k ⟶ X) := by
  letI : FiniteDimensional ℂ (simples C k ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  exact basisOfLinearIndependentOfCardEqFinrank' (simpleInclusion C X k)
    (simpleInclusion_independent C X k) (Fintype.card_fin _)

@[simp]
theorem simpleInclusionBasis_apply
    (X : C.Obj) (k : Fin (rank C))
    (t : Fin (Module.finrank ℂ (simples C k ⟶ X))) :
    simpleInclusionBasis C X k t = simpleInclusion C X k t := by
  let : FiniteDimensional ℂ (simples C k ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) t

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
  simp only [Preadditive.sum_comp, Linear.smul_comp] at h
  dsimp only [b] at h
  simp only [simpleInclusionBasis_apply, simpleInclusion, Category.assoc, Iso.inv_hom_id_assoc] at h
  have he : (∑ x, ((b.repr g) x) • (biproduct.ι (simplePiecesObject C X) ⟨k, x⟩ ≫
      biproduct.π (simplePiecesObject C X) ⟨k, t⟩)) = (b.repr g t) • 𝟙 (simples C k) := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro x _ hxt
      rw [biproduct.ι_π_ne (simplePiecesObject C X) (by simpa using hxt)]
      simp
    · simp
  rw [he] at h
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
  let : Simple (simples C k) := Ground.simples_simple C k
  let : FiniteDimensional ℂ (simples C k ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
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
    Ground.unitScalar C (rootTrace C g) =
      ∑ k, LinearMap.trace ℂ _ (Linear.rightComp ℂ (simples C k) g) * rootDimension C k := by
  classical
  let V := simplePiecesObject C X
  let e := simpleDecomposition C X
  let f : (⨁ V) ⟶ (⨁ V) := e.inv ≫ g ≫ e.hom
  have heq : rootTrace C g = rootTrace C f := by
    simpa [f, Category.assoc] using (rootTrace_cyclic C e.hom (e.inv ≫ g))
  obtain ⟨c, hc, ht⟩ := rootTrace_biproduct_simple C V (fun a => Ground.simples_simple C a.1) f
  rw [heq, ht]
  simp only [← groundUnitScalarEquiv_apply, map_sum, map_smul, smul_eq_mul, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  have hblock : ∀ t, biproduct.ι V ⟨k, t⟩ ≫ e.inv ≫ g ≫ e.hom ≫ biproduct.π V ⟨k, t⟩ =
      c ⟨k, t⟩ • 𝟙 (simples C k) := by
    intro t
    simpa [f, Category.assoc] using hc ⟨k, t⟩
  rw [(simpleHom_postcomp_trace C g (fun t => c ⟨k,t⟩) hblock), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  change c ⟨k, t⟩ * (groundUnitScalarEquiv C (rootTrace C (𝟙 (simples C k)))) =
    c ⟨k, t⟩ * rootDimension C k
  rw [groundUnitScalarEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Involutivity of every multiplicity operator implies ENO's trace-matrix
root-dimension eigenvector identity. -/
theorem enoTraceMatrix_eigenvector_of_involutions {i j : Fin (rank C)}
    (hinv : ∀ k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    ∑ k, enoTraceMatrix C i j k * rootDimension C k = rootDimension C i * rootDimension C j := by
  let X := simples C i ⊗ simples C j
  let d := rootTensorDefect C (simples C i) (simples C j)
  have hop (k : Fin (rank C)) :
      Linear.rightComp ℂ (simples C k) d.inv = (multiplicityDefect C i j k).toLinearMap := by
    ext f
    have h : multiplicityDefect C i j k (multiplicityDefect C i j k f) = f := by
      exact (congrArg (fun L => L f) (hinv k))
    have hs : (multiplicityDefect C i j k).symm f = multiplicityDefect C i j k f := by
      apply (multiplicityDefect C i j k).injective
      simp [h]
    simpa [multiplicityDefect, Linear.homCongr_apply, Linear.homCongr_symm_apply, d] using hs
  have ht := rootTrace_eq_simpleHom_trace_sum C d.inv
  rw [rootTrace_inverseDefect] at ht
  calc
    _ = ∑ k, LinearMap.trace ℂ _ (Linear.rightComp ℂ (simples C k) d.inv) * rootDimension C k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hop k]
      rfl
    _ = _ := ht.symm

end PropertyF.Ground.Dimensions

end
