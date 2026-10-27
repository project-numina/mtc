module
public import PropertyF.Ground.Calculus.Overlap

/-! Unitarity of the actual overlapping braid products. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus

/-- A star-algebra map between products of matrix algebras preserves
blockwise unitarity. -/
theorem starMap_preserves_block_unitary {r s : ℕ} {d : Fin r → ℕ} {q : Fin s → ℕ}
    (F : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ))
    (u : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, F u j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  have h : u * star u = 1 := by
    funext i
    exact Matrix.mem_unitaryGroup_iff.mp (hu i)
  intro j
  apply Matrix.mem_unitaryGroup_iff.mpr
  have hf := congrArg (fun x => x j) (congrArg F h)
  simpa only [map_mul, map_star, map_one, Pi.mul_apply, Pi.star_apply, Pi.one_apply] using hf

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Adding right identity strands preserves unitarity in any compatible
presentations of the actual braid-image algebras. -/
theorem addRight_braid_unitary (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ)
    (u : braidAlgebra X n) (hu : ∀ i, e u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, f (addRightBraidAlgebraIter X n k u) j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  simpa [addRightBlocksIterStarMap, addRightBlocksIter] using
    starMap_preserves_block_unitary (addRightBlocksIterStarMap X n k e f he hf) (e u) hu

/-- Adding left identity strands preserves unitarity in any compatible
presentations of the actual braid-image algebras. -/
theorem addLeft_braid_unitary (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hf : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ)
    (u : braidAlgebra X n) (hu : ∀ i, e u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, f (addLeftBraidAlgebraIter X n k u) j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  simpa [addLeftBlocksIterStarMap, addLeftBlocksIter] using
    starMap_preserves_block_unitary (addLeftBlocksIterStarMap X n k e f he hf) (e u) hu

/-- Successive actual overlapping products remain blockwise unitary. The
presentations may be chosen independently at every strand count. -/
theorem overlapProduct_unitary (X : C) (t : ℕ)
    (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℕ)
    (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
      ∀ i, Matrix (Fin (d n i)) (Fin (d n i)) ℂ)
    (he : ∀ n g i, e n (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d n i)) ℂ)
    (u : braidAlgebra X t) (hu : ∀ i, e t u i ∈ Matrix.unitaryGroup (Fin (d t i)) ℂ) :
    ∀ k i, e (overlapIndex t k) (overlapProduct X t u k) i ∈
      Matrix.unitaryGroup (Fin (d (overlapIndex t k) i)) ℂ := by
  intro k
  induction k with
  | zero => exact hu
  | succ k ih =>
    intro i
    rw [overlapProduct, map_mul, Pi.mul_apply]
    apply Submonoid.mul_mem
    · exact addRight_braid_unitary X (overlapIndex t k) (t + 1)
        (e _) (e _) (he _) (he _) _ ih i
    · have hr := addLeft_braid_unitary X t ((k + 1) * (t + 1))
        (e t) (e _) (he t) (he _) u hu
      have hcast : ∀ (a b : ℕ) (h : a = b)
          (f : braidAlgebra X t →ₐ[ℂ] braidAlgebra X b),
          (∀ j, e b (f u) j ∈ Matrix.unitaryGroup (Fin (d b j)) ℂ) →
          ∀ j, e a ((Eq.mpr (congrArg (fun n => braidAlgebra X t →ₐ[ℂ] braidAlgebra X n) h) f) u) j ∈
            Matrix.unitaryGroup (Fin (d a j)) ℂ := by
        intro a b h f hunit
        cases h
        exact hunit
      have hs : ∀ j, e (overlapIndex t (k + 1)) (overlapRight X t k u) j ∈
          Matrix.unitaryGroup (Fin (d (overlapIndex t (k + 1)) j)) ℂ := by
        exact hcast _ _ (overlapIndex_formula t (k + 1)) _ hr
      exact hs i

/-- Finite actual braid images provide presentations in which every repeated
overlap of a block-unitary element is block-unitary. -/
theorem exists_unitary_overlap_presentations (X : C)
    (hfinite : ∀ n, Finite (braidImage X n)) :
    ∃ (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℕ)
      (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
        ∀ i, Matrix (Fin (d n i)) (Fin (d n i)) ℂ),
      (∀ n i, NeZero (d n i)) ∧
      (∀ n g i, e n (groupInImage (braidEndRepresentation X n) g) i ∈
        Matrix.unitaryGroup (Fin (d n i)) ℂ) ∧
      ∀ t (u : braidAlgebra X t),
        (∀ i, e t u i ∈ Matrix.unitaryGroup (Fin (d t i)) ℂ) →
        ∀ k i, e (overlapIndex t k) (overlapProduct X t u k) i ∈
          Matrix.unitaryGroup (Fin (d (overlapIndex t k) i)) ℂ := by
  classical
  choose r d e hd he using fun n => braidAlgebra_unitary_blocks X n (hfinite n)
  exact ⟨r, d, e, hd, he, fun t u hu => overlapProduct_unitary X t r d e he u hu⟩

end PropertyF.Ground.Calculus
