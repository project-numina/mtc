module
public import PropertyF.Ground.Calculus.Intertwining
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import PropertyF.Ground.Cabling.Strands

/-! Algebra maps induced by intertwiners of categorical group images. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus

variable {G H A B : Type*} [Group G] [Group H]
  [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

@[simp] theorem groupInImage_val (ρ : G →* A) (g : G) :
    (groupInImage ρ g : A) = ρ g := by
  change MonoidAlgebra.lift ℂ A G ρ (MonoidAlgebra.of ℂ G g) = ρ g
  exact MonoidAlgebra.lift_of ρ g

/-- An algebra map intertwining group representations carries the image
algebra into the target image algebra. -/
def imageAlgebraMap (ρ : G →* A) (σ : H →* B) (τ : G →* H)
    (F : A →ₐ[ℂ] B) (hF : ∀ g, F (ρ g) = σ (τ g)) :
    groupImageAlgebra ρ →ₐ[ℂ] groupImageAlgebra σ := by
  let f := F.comp (groupImageAlgebra ρ).val
  refine f.codRestrict _ ?_
  intro x
  have hx : (x : A) ∈ Submodule.span ℂ (Set.range ρ) := by
    rw [← groupImageAlgebra_toSubmodule]
    exact x.property
  have hspan : Submodule.span ℂ (Set.range ρ) ≤
      ((groupImageAlgebra σ).toSubmodule.comap F.toLinearMap) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change F (ρ g) ∈ groupImageAlgebra σ
    rw [hF]
    simpa using (groupInImage σ (τ g)).property
  exact hspan hx

/-- The induced algebra map intertwines the image-group representations. -/
theorem imageAlgebraMap_group (ρ : G →* A) (σ : H →* B) (τ : G →* H)
    (F : A →ₐ[ℂ] B) (hF : ∀ g, F (ρ g) = σ (τ g)) (g : G) :
    imageAlgebraMap ρ σ τ F hF (groupInImage ρ g) = groupInImage σ (τ g) := by
  apply Subtype.ext
  change F (groupInImage ρ g : A) = (groupInImage σ (τ g) : B)
  simpa using hF g

universe v u v' u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [Linear ℂ C] [Linear ℂ D]

/-- A complex-linear additive functor acts by algebra homomorphisms on
endomorphisms. -/
def functorEndAlgHom (F : C ⥤ D) [F.Additive] [F.Linear ℂ] (X : C) :
    End X →ₐ[ℂ] End (F.obj X) where
  toFun := F.mapEnd X
  map_one' := (F.mapEnd X).map_one
  map_mul' := (F.mapEnd X).map_mul
  map_zero' := by
    apply End.ext
    simp
  map_add' x y := by
    apply End.ext
    simp
  commutes' z := by
    apply End.ext
    simp [Algebra.algebraMap_eq_smul_one]

variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [MonoidalLinear ℂ C]

/-- Adding an identity strand on the left induces an algebra map on the
actual braid-image spans. -/
def addLeftBraidAlgebra (X : C) (n : ℕ) : braidAlgebra X n →ₐ[ℂ] braidAlgebra X (n + 1) :=
  imageAlgebraMap (braidEndRepresentation X n) (braidEndRepresentation X (n + 1))
    (addLeftStrand X n) (functorEndAlgHom (tensorLeft X) (tensorPower X (n + 2))) (by
      intro g
      rfl)

/-- The identity-strand algebra map carries each actual braid to its inserted
copy. -/
theorem addLeftBraidAlgebra_group (X : C) (n : ℕ) (g : braidImage X n) :
    addLeftBraidAlgebra X n (groupInImage (braidEndRepresentation X n) g) =
      groupInImage (braidEndRepresentation X (n + 1)) (addLeftStrand X n g) := by
  apply imageAlgebraMap_group

/-- Adding a left strand, expressed in independently chosen unitary matrix
blocks at consecutive strand numbers. -/
def addLeftBlockMap (X : C) (n : ℕ) {r s : ℕ} {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + 1) ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ]
      (∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) :=
  f.toAlgHom.comp ((addLeftBraidAlgebra X n).comp e.symm.toAlgHom)

set_option backward.isDefEq.respectTransparency false in
/-- The actual left-strand map preserves the adjoint in any two unitary
block presentations, regardless of their individual averaging choices. -/
theorem addLeftBlockMap_star (X : C) (n : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + 1) ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + 1)) g) i ∈
      Matrix.unitaryGroup (Fin (k i)) ℂ)
    (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    addLeftBlockMap X n e f (star x) = star (addLeftBlockMap X n e f x) := by
  apply presented_intertwiner_map_star (braidEndRepresentation X n)
    (braidEndRepresentation X (n + 1)) (addLeftStrand X n) e f he hf
    (addLeftBlockMap X n e f)
  intro g
  change f (addLeftBraidAlgebra X n (e.symm (e (groupInImage (braidEndRepresentation X n) g)))) = _
  rw [e.symm_apply_apply, addLeftBraidAlgebra_group]
  rfl

/-- Bundled star algebra map for the left identity-strand embedding. -/
def addLeftBlockStarMap (X : C) (n : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {k : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + 1) ≃ₐ[ℂ] ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + 1)) g) i ∈
      Matrix.unitaryGroup (Fin (k i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (Fin (k i)) (Fin (k i)) ℂ) where
  toAlgHom := addLeftBlockMap X n e f
  map_star' := addLeftBlockMap_star X n e f he hf

end PropertyF.Ground.Calculus
