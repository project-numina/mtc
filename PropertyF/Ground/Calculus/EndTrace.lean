module
public import PropertyF.Ground.Calculus.EndBlocks
public import PropertyF.Ground.Dimensions.BiproductTrace

/-! The pivotal trace in the simple-constituent matrix decomposition. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Scalar identification for a chosen simple object. -/
def groundSimpleScalar (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    End (Ground.simples C i) ≃ₐ[ℂ] ℂ := by
  let _ : Simple (Ground.simples C i) := Ground.simples_simple C i
  let _ : FiniteDimensional ℂ (Ground.simples C i ⟶ Ground.simples C i) :=
    Ground.IsFusionCategory.hom_finite _ _
  exact simpleEndScalar _

/-- Evaluating a simple endomorphism at its Schur scalar recovers the morphism. -/
theorem groundSimpleScalar_smul_id (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) (a : End (Ground.simples C i)) :
    (groundSimpleScalar C i a) • 𝟙 (Ground.simples C i) = a.asHom := by
  have h := (groundSimpleScalar C i).symm_apply_apply a
  change (algebraMap ℂ (End (Ground.simples C i))) (groundSimpleScalar C i a) = a at h
  have h' := congrArg End.asHom h
  simpa [Algebra.algebraMap_eq_smul_one] using h'

set_option backward.isDefEq.respectTransparency false in
/-- A diagonal matrix coefficient is the scalar of the corresponding simple
biproduct component of the transported endomorphism. -/
theorem groundEndBlockEquiv_diagonal (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (m : Fin (Ground.rank C) → ℕ)
    (e : X ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1))
    (a : End X) (i : Fin (Ground.rank C)) (j : Fin (m i)) :
    groundEndBlockEquiv C X m e a i j j =
      groundSimpleScalar C i (End.of
        (biproduct.ι (fun p : Σ i, Fin (m i) => Ground.simples C p.1) ⟨i, j⟩ ≫
          e.inv ≫ a.asHom ≫ e.hom ≫
          biproduct.π (fun p : Σ i, Fin (m i) => Ground.simples C p.1) ⟨i, j⟩)) := by
  classical
  simp [groundEndBlockEquiv, orthogonalEndBlocks, isoEndAlgEquiv,
    simpleFiberEquiv, groundSimpleScalar, HomOrthogonal.matrixDecompositionAddEquiv, HomOrthogonal.matrixDecomposition,
    Matrix.reindexAlgEquiv, Matrix.reindexRingEquiv, Matrix.reindexAddEquiv,
    Matrix.reindex, Category.assoc, biproduct.components]

set_option backward.isDefEq.respectTransparency false in
/-- The actual pivotal trace on a fusion-category endomorphism is the sum of
simple categorical dimensions times the ordinary traces of its constituent
multiplicity blocks. -/
theorem pivotalTrace_groundEndBlocks (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (X : C.Obj) (m : Fin (Ground.rank C) → ℕ)
    (e : X ≅ ⨁ (fun p : Σ i, Fin (m i) => Ground.simples C p.1)) (a : End X) :
    scalar (p.rightTrace a.asHom) = ∑ i,
      scalar (p.rightTrace (𝟙 (Ground.simples C i))) *
        (groundEndBlockEquiv C X m e a i).trace := by
  classical
  let F : (Σ i, Fin (m i)) → C.Obj := fun q => Ground.simples C q.1
  let z : (⨁ F) ⟶ (⨁ F) := e.inv ≫ a.asHom ≫ e.hom
  have hz : p.rightTrace z = p.rightTrace a.asHom := by
    have h := p.rightTrace_cyclic e.inv (a.asHom ≫ e.hom)
    simpa [z, Category.assoc] using h
  calc
    scalar (p.rightTrace a.asHom) = scalar (p.rightTrace z) := by rw [hz]
    _ = ∑ q, scalar (p.rightTrace (biproduct.ι F q ≫ z ≫ biproduct.π F q)) := by
      rw [Dimensions.rightTrace_biproduct F p z, map_sum]
    _ = ∑ q : Σ i, Fin (m i),
        (groundEndBlockEquiv C X m e a q.1 q.2 q.2) *
          scalar (p.rightTrace (𝟙 (Ground.simples C q.1))) := by
      apply Finset.sum_congr rfl
      rintro ⟨i, j⟩ _
      rw [groundEndBlockEquiv_diagonal]
      simp only [z, Category.assoc]
      let b : End (Ground.simples C i) := End.of
        (biproduct.ι F ⟨i,j⟩ ≫ e.inv ≫ a.asHom ≫ e.hom ≫ biproduct.π F ⟨i,j⟩)
      change scalar (p.rightTrace b.asHom) = groundSimpleScalar C i b * _
      rw [← groundSimpleScalar_smul_id C i b, p.rightTrace_smul, map_smul]
      simp
    _ = ∑ i, scalar (p.rightTrace (𝟙 (Ground.simples C i))) *
        (groundEndBlockEquiv C X m e a i).trace := by
      rw [Fintype.sum_sigma]
      simp [Matrix.trace, Finset.mul_sum, mul_comm]

end PropertyF.Ground.Calculus
