module
public import MTC.Fusion.Multiplicity
public import MTC.CategoryTheory.Dimensions.Trace
public import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
public import Mathlib.CategoryTheory.Conj
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Endomorphism algebras of finite sums

An endomorphism algebra of a finite sum of orthogonal objects decomposes into matrix
blocks. `groundEndBlockEquiv` applies this to the simple objects of a fusion category.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

section Biproduct
variable [HasFiniteBiproducts C]

open scoped Classical in
/-- Orthogonal direct-sum endomorphisms decompose as matrix blocks over the
endomorphism algebras of the constituents. -/
def orthogonalEndBlocks {ι α : Type} [Fintype α]
    (S : ι → C) (f : α → ι) (hS : HomOrthogonal S) :
    End (⨁ fun a => S (f a)) ≃ₐ[ℂ]
      ∀ i : ι, Matrix (f ⁻¹' {i}) (f ⁻¹' {i}) (End (S i)) := by
  classical
  let e := (End.linearEquiv (R := ℂ)).trans (hS.matrixDecompositionLinearEquiv (R := ℂ) (f := f) (g := f))
  exact
    { e.toEquiv with
      map_add' := e.map_add
      map_mul' := by
        intro x y
        change e (x * y) = e x * e y
        apply funext
        intro i
        exact hS.matrixDecomposition_comp y.asHom x.asHom i
      commutes' := by
        intro z
        change e (algebraMap ℂ _ z) = _
        rw [Algebra.algebraMap_eq_smul_one, e.map_smul]
        rw [Algebra.algebraMap_eq_smul_one]
        congr 1
        apply funext
        intro i
        exact hS.matrixDecomposition_id i }

end Biproduct

section Conjugation

variable {X Y : C} (e : X ≅ Y)

/-- Conjugation by a categorical isomorphism is a complex-algebra equivalence
on endomorphisms. -/
def isoEndAlgEquiv : End X ≃ₐ[ℂ] End Y where
  __ := e.conj.toEquiv
  map_mul' := e.conj.map_mul
  map_add' a b := by
    apply End.ext
    simp
  commutes' z := by
    apply End.ext
    simp [Algebra.algebraMap_eq_smul_one]

end Conjugation

section PivotalTrace

variable {X Y : C} [MonoidalCategory C] [RightRigidCategory C]

omit [Preadditive C] [Linear ℂ C] in
/-- Pivotal trace is unchanged by categorical conjugation. -/
theorem rightTrace_iso_conj (e : X ≅ Y) (p : Dimensions.PivotalStructure (C := C)) (a : End X) :
    p.rightTrace (e.conj a).asHom = p.rightTrace a.asHom := by
  simpa [Iso.conj_apply_asHom, Category.assoc] using
    p.rightTrace_cyclic e.inv (a.asHom ≫ e.hom)

end PivotalTrace

variable (D : BraidedFusionCategory.{v,u})

/-- The chosen nonisomorphic simple representatives are Hom-orthogonal. -/
theorem groundSimples_orthogonal : HomOrthogonal (Ground.simples D) :=
  let _ : ∀ i, Simple (Ground.simples D i) := Ground.simples_simple D
  fun _i _j hij => subsingleton_of_forall_eq 0 fun f => Classical.byContradiction fun hf =>
    hij (Ground.simples_injective D ⟨let _ : IsIso f := isIso_of_hom_simple hf; asIso f⟩)

/-- The family containing `m i` copies of each chosen simple object. -/
abbrev simpleCopies (m : Fin (Ground.rank D) → ℕ)
    (p : Σ i, Fin (m i)) : D.Obj := Ground.simples D p.1

/-- The occurrences of label `i` in a dependent sum are indexed by `Fin (m i)`. -/
def simpleFiberEquiv {ι : Type} (m : ι → ℕ) (i : ι) :
    {p : Σ j, Fin (m j) // p.1 = i} ≃ Fin (m i) where
  toFun p := p.2 ▸ p.1.2
  invFun k := ⟨⟨i, k⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨j, k⟩, h⟩
    cases h
    rfl
  right_inv k := rfl

/-- A chosen simple-object decomposition gives the corresponding complex
matrix-block decomposition of its endomorphism algebra. -/
def groundEndBlockEquiv {X : D.Obj}
    {m : Fin (Ground.rank D) → ℕ}
    (e : X ≅ ⨁ (simpleCopies D m)) :
    End X ≃ₐ[ℂ] ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ := by
  classical
  let _ : HasFiniteBiproducts D.Obj := inferInstance
  let _ : ∀ i, Simple (Ground.simples D i) := Ground.simples_simple D
  let _ : ∀ i, FiniteDimensional ℂ (Ground.simples D i ⟶ Ground.simples D i) :=
    fun i => Ground.IsFusionCategory.hom_finite _ _
  let _ : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
  let f : (Σ i, Fin (m i)) → Fin (Ground.rank D) := Sigma.fst
  let decomp := orthogonalEndBlocks (Ground.simples D) f (groundSimples_orthogonal D)
  let scalars : (∀ i, Matrix (f ⁻¹' {i}) (f ⁻¹' {i}) (End (Ground.simples D i))) ≃ₐ[ℂ]
      (∀ i, Matrix (f ⁻¹' {i}) (f ⁻¹' {i}) ℂ) :=
    AlgEquiv.piCongrRight fun i => (simpleEndScalar (k := ℂ) (Ground.simples D i)).mapMatrix
  let reindex : (∀ i, Matrix (f ⁻¹' {i}) (f ⁻¹' {i}) ℂ) ≃ₐ[ℂ]
      (∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :=
    AlgEquiv.piCongrRight fun i => Matrix.reindexAlgEquiv ℂ ℂ (simpleFiberEquiv m i)
  exact (isoEndAlgEquiv e).trans (decomp.trans (scalars.trans reindex))

end PropertyF.Ground.Calculus
