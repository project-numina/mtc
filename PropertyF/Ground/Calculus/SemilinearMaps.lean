module
public import PropertyF.Ground.Calculus.GaloisBlocks
public import PropertyF.Ground.Calculus.RightStrand

/-! Intertwiners between semilinearly transported unitary presentations. -/

@[expose] public noncomputable section
namespace PropertyF.Ground.Calculus

variable {A B V W : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [Ring V] [Algebra ℂ V] [Ring W] [Algebra ℂ W]

/-- The inverse of a semilinear ring equivalence is semilinear for the
inverse scalar automorphism. -/
theorem semilinear_symm_smul (σ : ℂ ≃+* ℂ) (e : A ≃+* V)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a) (z : ℂ) (v : V) :
    e.symm (z • v) = σ.symm z • e.symm v := by
  apply e.injective
  simp only [e.apply_symm_apply, he, σ.apply_symm_apply]

/-- Conjugating a complex-linear algebra map by two equivalences with the
same scalar twist gives an ordinary complex-linear algebra map. -/
def semilinearIntertwiner (σ : ℂ ≃+* ℂ) (e : A ≃+* V) (f : B ≃+* W)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a)
    (hf : ∀ (z : ℂ) b, f (z • b) = σ z • f b) (F : A →ₐ[ℂ] B) : V →ₐ[ℂ] W where
  toFun x := f (F (e.symm x))
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, semilinear_symm_smul σ e he, map_one,
      map_smul, map_one, hf, map_one, σ.apply_symm_apply, ← Algebra.algebraMap_eq_smul_one]

/-- A semilinear equivalence still sends a spanning group image to a complex
spanning family, since the scalar automorphism is surjective. -/
theorem semilinear_presented_group_span {G : Type*} [Group G]
    (ρ : G →* A) {r : ℕ} {d : Fin r → ℕ} (σ : ℂ ≃+* ℂ)
    (e : groupImageAlgebra ρ ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a) :
    Submodule.span ℂ (Set.range (e.toMonoidHom.comp (groupInImage ρ))) = ⊤ := by
  classical
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨a, rfl⟩ := e.surjective x
  have ha : a ∈ Submodule.span ℂ (Set.range (groupInImage ρ)) := by
    rw [groupInImage_span]
    exact Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span (Set.mem_range_self g)
  | zero => simp only [map_zero]; exact (Submodule.zero_mem (Submodule.span ℂ
      (Set.range (e.toMonoidHom.comp (groupInImage ρ)))))
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul z x hx ih =>
    rw [he]
    exact Submodule.smul_mem _ (σ z) ih

/-- Intertwiners of semilinearly transported unitary group presentations are
star-preserving, even when the two presentations use different bases. -/
theorem semilinear_intertwiner_star {G H : Type*} [Group G] [Group H]
    (ρ : G →* A) (η : H →* B) (τ : G →* H) (σ : ℂ ≃+* ℂ)
    {r s : ℕ} {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : groupImageAlgebra ρ ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : groupImageAlgebra η ≃+* ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a)
    (hf : ∀ (z : ℂ) b, f (z • b) = σ z • f b)
    (heunit : ∀ g i, e (groupInImage ρ g) i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hfunit : ∀ h i, f (groupInImage η h) i ∈ Matrix.unitaryGroup (Fin (q i)) ℂ)
    (F : groupImageAlgebra ρ →ₐ[ℂ] groupImageAlgebra η)
    (hF : ∀ g, F (groupInImage ρ g) = groupInImage η (τ g))
    (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    semilinearIntertwiner σ e f he hf F (star x) =
      star (semilinearIntertwiner σ e f he hf F x) := by
  let ρ' := e.toMonoidHom.comp (groupInImage ρ)
  let η' := f.toMonoidHom.comp (groupInImage η)
  apply map_star_of_group_span ρ' η' τ (semilinearIntertwiner σ e f he hf F)
    (semilinear_presented_group_span ρ σ e he)
  · exact unitary_block_star_inv ρ' heunit
  · exact unitary_block_star_inv η' hfunit
  · intro g
    change f (F (e.symm (e (groupInImage ρ g)))) = f (groupInImage η (τ g))
    rw [e.symm_apply_apply, hF]

universe v u
variable {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.MonoidalCategory C]
  [CategoryTheory.BraidedCategory C] [CategoryTheory.Preadditive C] [CategoryTheory.Linear ℂ C]
  [CategoryTheory.MonoidalPreadditive C] [CategoryTheory.MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- Repeated left identity-strand insertion is a star-algebra map in any two
unitary Galois-transported block presentations. -/
def galoisLeftBlocksIterStarMap (X : C) (n k : ℕ) (σ : ℂ ≃+* ℂ)
    {r s : ℕ} {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃+* ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a)
    (hf : ∀ (z : ℂ) a, f (z • a) = σ z • f a)
    (heunit : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hfunit : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ) where
  toAlgHom := semilinearIntertwiner σ e f he hf (addLeftBraidAlgebraIter X n k)
  map_star' := semilinear_intertwiner_star (braidEndRepresentation X n)
    (braidEndRepresentation X (n + k)) (addLeftStrands X n k) σ e f he hf heunit hfunit
    (addLeftBraidAlgebraIter X n k) (addLeftBraidAlgebraIter_group X n k)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right identity-strand insertion is a star-algebra map in any two
unitary Galois-transported block presentations. -/
def galoisRightBlocksIterStarMap (X : C) (n k : ℕ) (σ : ℂ ≃+* ℂ)
    {r s : ℕ} {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃+* ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a)
    (hf : ∀ (z : ℂ) a, f (z • a) = σ z • f a)
    (heunit : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hfunit : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ) where
  toAlgHom := semilinearIntertwiner σ e f he hf (addRightBraidAlgebraIter X n k)
  map_star' := semilinear_intertwiner_star (braidEndRepresentation X n)
    (braidEndRepresentation X (n + k)) (addRightStrands X n k) σ e f he hf heunit hfunit
    (addRightBraidAlgebraIter X n k) (addRightBraidAlgebraIter_group X n k)

end PropertyF.Ground.Calculus
