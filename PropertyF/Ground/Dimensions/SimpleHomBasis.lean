module
public import PropertyF.Ground.Dimensions.DefectTrace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

def simpleInclusion (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (k : Fin (Ground.rank C)) (t : Fin (Module.finrank ℂ (Ground.simples C k ⟶ X))) :
    Ground.simples C k ⟶ X :=
  biproduct.ι (simplePiecesObject C X) ⟨k, t⟩ ≫ (simpleDecomposition C X).inv

set_option backward.isDefEq.respectTransparency false in
theorem simpleInclusion_independent (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (Ground.rank C)) :
    LinearIndependent ℂ (simpleInclusion C X k) := by
  classical
  letI : Simple (Ground.simples C k) := Ground.simples_simple C k
  apply Fintype.linearIndependent_iff.mpr
  intro g hg t
  have h := congrArg (fun f : Ground.simples C k ⟶ X =>
    f ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩) hg
  simp only [Preadditive.sum_comp, Linear.smul_comp, zero_comp] at h
  have hh : g t • 𝟙 (Ground.simples C k) = 0 := by
    simp [simpleInclusion, Category.assoc] at h
    have he : (∑ x, g x • (biproduct.ι (simplePiecesObject C X) ⟨k, x⟩ ≫
        biproduct.π (simplePiecesObject C X) ⟨k, t⟩)) = g t • 𝟙 (Ground.simples C k) := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro x _ hxt
        rw [biproduct.ι_π_ne (simplePiecesObject C X) (by simpa using hxt)]
        simp
      · simp
    rw [he] at h
    exact h
  have := (smul_left_injective ℂ (id_nonzero (Ground.simples C k))) (by simpa using hh : g t • 𝟙 _ = (0 : ℂ) • 𝟙 _)
  exact this

/-- The canonical summand inclusions form a basis of each simple Hom space. -/
def simpleInclusionBasis (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (Ground.rank C)) :
    Module.Basis (Fin (Module.finrank ℂ (Ground.simples C k ⟶ X))) ℂ (Ground.simples C k ⟶ X) := by
  letI : FiniteDimensional ℂ (Ground.simples C k ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  exact basisOfLinearIndependentOfCardEqFinrank' (simpleInclusion C X k)
    (simpleInclusion_independent C X k) (Fintype.card_fin _)

@[simp]
theorem simpleInclusionBasis_apply (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (Ground.rank C))
    (t : Fin (Module.finrank ℂ (Ground.simples C k ⟶ X))) :
    simpleInclusionBasis C X k t = simpleInclusion C X k t := by
  letI : FiniteDimensional ℂ (Ground.simples C k ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) t

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates in the simple-inclusion basis are the scalar diagonal
projections of the morphism. -/
theorem simpleInclusionBasis_projection (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (Ground.rank C)) (g : Ground.simples C k ⟶ X)
    (t : Fin (Module.finrank ℂ (Ground.simples C k ⟶ X))) :
    ((simpleInclusionBasis C X k).repr g t) • 𝟙 (Ground.simples C k) =
      g ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩ := by
  classical
  let b := simpleInclusionBasis C X k
  have h := congrArg (fun f : Ground.simples C k ⟶ X =>
    f ≫ (simpleDecomposition C X).hom ≫ biproduct.π (simplePiecesObject C X) ⟨k, t⟩) (b.sum_repr g)
  simp only [Preadditive.sum_comp, Linear.smul_comp] at h
  dsimp only [b] at h
  simp only [simpleInclusionBasis_apply, simpleInclusion, Category.assoc, Iso.inv_hom_id_assoc] at h
  have he : (∑ x, ((b.repr g) x) • (biproduct.ι (simplePiecesObject C X) ⟨k, x⟩ ≫
      biproduct.π (simplePiecesObject C X) ⟨k, t⟩)) = (b.repr g t) • 𝟙 (Ground.simples C k) := by
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
theorem simpleHom_postcomp_trace (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (k : Fin (Ground.rank C)) (g : X ⟶ X)
    (c : Fin (Module.finrank ℂ (Ground.simples C k ⟶ X)) → ℂ)
    (hc : ∀ t, biproduct.ι (simplePiecesObject C X) ⟨k, t⟩ ≫
      (simpleDecomposition C X).inv ≫ g ≫ (simpleDecomposition C X).hom ≫
        biproduct.π (simplePiecesObject C X) ⟨k, t⟩ = c t • 𝟙 (Ground.simples C k)) :
    LinearMap.trace ℂ _ (Linear.rightComp ℂ (Ground.simples C k) g) = ∑ t, c t := by
  classical
  letI : Simple (Ground.simples C k) := Ground.simples_simple C k
  letI : FiniteDimensional ℂ (Ground.simples C k ⟶ X) := Ground.IsFusionCategory.hom_finite _ _
  rw [LinearMap.trace_eq_matrix_trace ℂ (simpleInclusionBasis C X k)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro t _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Linear.rightComp_apply,
    simpleInclusionBasis_apply]
  apply smul_left_injective ℂ (id_nonzero (Ground.simples C k))
  have hh := simpleInclusionBasis_projection C X k (simpleInclusion C X k t ≫ g) t
  simpa [simpleInclusion, Category.assoc, hc t] using hh

set_option backward.isDefEq.respectTransparency false in
/-- The natural-root categorical trace equals the dimension-weighted sum of
ordinary traces on the simple Hom spaces. -/
theorem rootTrace_eq_simpleHom_trace_sum (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (g : X ⟶ X) :
    Ground.unitScalar C (rootTrace C g) =
      ∑ k, LinearMap.trace ℂ _ (Linear.rightComp ℂ (Ground.simples C k) g) * rootDimension C k := by
  classical
  let V := simplePiecesObject C X
  let e := simpleDecomposition C X
  let f : (⨁ V) ⟶ (⨁ V) := e.inv ≫ g ≫ e.hom
  have heq : rootTrace C g = rootTrace C f := by
    have h := rootTrace_cyclic C e.hom (e.inv ≫ g)
    simpa [f, Category.assoc] using h
  obtain ⟨c, hc, ht⟩ := rootTrace_biproduct_simple C V (fun a => Ground.simples_simple C a.1) f
  rw [heq, ht]
  simp only [← groundUnitScalarEquiv_apply, map_sum, map_smul, smul_eq_mul, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  have hblock : ∀ t, biproduct.ι V ⟨k, t⟩ ≫ e.inv ≫ g ≫ e.hom ≫ biproduct.π V ⟨k, t⟩ =
      c ⟨k, t⟩ • 𝟙 (Ground.simples C k) := by
    intro t
    simpa [f, Category.assoc] using hc ⟨k, t⟩
  have hs := simpleHom_postcomp_trace C X k g (fun t => c ⟨k,t⟩) hblock
  rw [hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  change c ⟨k, t⟩ * (groundUnitScalarEquiv C (rootTrace C (𝟙 (Ground.simples C k)))) =
    c ⟨k, t⟩ * rootDimension C k
  rw [groundUnitScalarEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Involutivity of every multiplicity operator implies ENO's trace-matrix
root-dimension eigenvector identity. -/
theorem enoTraceMatrix_eigenvector_of_involutions
    (C : Ground.BraidedFusionCategory.{v,u}) (i j : Fin (Ground.rank C))
    (hinv : ∀ k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    ∑ k, enoTraceMatrix C i j k * rootDimension C k = rootDimension C i * rootDimension C j := by
  let X := Ground.simples C i ⊗ Ground.simples C j
  let d := rootTensorDefect C (Ground.simples C i) (Ground.simples C j)
  have hop (k : Fin (Ground.rank C)) :
      Linear.rightComp ℂ (Ground.simples C k) d.inv = (multiplicityDefect C i j k).toLinearMap := by
    ext f
    have h : multiplicityDefect C i j k (multiplicityDefect C i j k f) = f := by
      have hh := congrArg (fun L => L f) (hinv k)
      exact hh
    have hs : (multiplicityDefect C i j k).symm f = multiplicityDefect C i j k f := by
      apply (multiplicityDefect C i j k).injective
      simp [h]
    simpa [multiplicityDefect, Linear.homCongr_apply, Linear.homCongr_symm_apply, d] using hs
  have ht := rootTrace_eq_simpleHom_trace_sum C X d.inv
  rw [rootTrace_inverseDefect] at ht
  calc
    _ = ∑ k, LinearMap.trace ℂ _ (Linear.rightComp ℂ (Ground.simples C k) d.inv) * rootDimension C k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hop k]
      rfl
    _ = _ := ht.symm

end PropertyF.Ground.Dimensions
