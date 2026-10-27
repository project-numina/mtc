module
public import PropertyF.Ground.Calculus.SemilinearMaps
public import PropertyF.Ground.Calculus.OverlapBound
public import PropertyF.Ground.Calculus.GaloisTraceBound

/-! Overlapping products in semilinearly transported braid blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- Right identity strands preserve unitary elements in transported blocks. -/
theorem galois_addRight_unitary (X : C) (n k : ℕ) (σ : ℂ ≃+* ℂ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃+* ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a)
    (hf : ∀ (z : ℂ) a, f (z • a) = σ z • f a)
    (heunit : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hfunit : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ)
    (u : braidAlgebra X n) (hu : ∀ i, e u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, f (addRightBraidAlgebraIter X n k u) j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  simpa [galoisRightBlocksIterStarMap, semilinearIntertwiner] using
    starMap_preserves_block_unitary (galoisRightBlocksIterStarMap X n k σ e f he hf heunit hfunit) (e u) hu

set_option backward.isDefEq.respectTransparency false in
/-- Left identity strands preserve unitary elements in transported blocks. -/
theorem galois_addLeft_unitary (X : C) (n k : ℕ) (σ : ℂ ≃+* ℂ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃+* ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : ∀ (z : ℂ) a, e (z • a) = σ z • e a)
    (hf : ∀ (z : ℂ) a, f (z • a) = σ z • f a)
    (heunit : ∀ g i, e (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hfunit : ∀ g i, f (groupInImage (braidEndRepresentation X (n + k)) g) i ∈
      Matrix.unitaryGroup (Fin (q i)) ℂ)
    (u : braidAlgebra X n) (hu : ∀ i, e u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, f (addLeftBraidAlgebraIter X n k u) j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  simpa [galoisLeftBlocksIterStarMap, semilinearIntertwiner] using
    starMap_preserves_block_unitary (galoisLeftBlocksIterStarMap X n k σ e f he hf heunit hfunit) (e u) hu

/-- Every iterated actual overlap stays unitary in independently chosen
semilinear Galois block presentations. -/
theorem galois_overlapProduct_unitary (X : C) (t : ℕ) (σ : ℂ ≃+* ℂ)
    (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℕ)
    (e : ∀ n, braidAlgebra X n ≃+* ∀ i, Matrix (Fin (d n i)) (Fin (d n i)) ℂ)
    (he : ∀ n (z : ℂ) a, e n (z • a) = σ z • e n a)
    (heunit : ∀ n g i, e n (groupInImage (braidEndRepresentation X n) g) i ∈
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
    · exact galois_addRight_unitary X (overlapIndex t k) (t + 1) σ
        (e _) (e _) (he _) (he _) (heunit _) (heunit _) _ ih i
    · have hr := galois_addLeft_unitary X t ((k + 1) * (t + 1)) σ
        (e t) (e _) (he t) (he _) (heunit t) (heunit _) u hu
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

/-- Galois-transformed pivotal trace on an actual braid algebra. -/
def galoisActualBraidTrace (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ)
    (n : ℕ) (a : braidAlgebra X n) : ℂ := σ (actualBraidTrace C X p n a)

/-- The sharp Galois trace bound follows from the intrinsic overlap identity;
unitarity of all overlaps is proved for arbitrary transported presentations. -/
theorem galois_sharp_trace_bound_of_overlap_identity
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) (t : ℕ)
    (r : ℕ → ℕ) (size : ∀ n, Fin (r n) → ℕ)
    (T : ∀ n, braidAlgebra X n ≃+* ∀ i, Matrix (Fin (size n i)) (Fin (size n i)) ℂ)
    (hsmul : ∀ n (z : ℂ) a, T n (z • a) = σ z • T n a)
    (hunit : ∀ n g i, T n (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (size n i)) ℂ)
    (hbound : ∀ n (a : braidAlgebra X n),
      (∀ i, T n a i ∈ Matrix.unitaryGroup (Fin (size n i)) ℂ) →
      ‖galoisActualBraidTrace C X p σ n a‖ ≤ Ground.fpDimension C X ^ (n + 2))
    (u : braidAlgebra X t) (hu : ∀ i, T t u i ∈ Matrix.unitaryGroup (Fin (size t i)) ℂ)
    (hrec : ∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        actualBraidTrace C X p t u ^ (k + 1)) :
    ‖galoisActualBraidTrace C X p σ t u‖ ≤
      ‖σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))‖ *
        Ground.fpDimension C X ^ (t + 1) := by
  have hδ₀ : Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) ≠ 0 := by
    intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply (Dimensions.groundUnitScalarEquiv C).injective
    simpa using h
  have hδ : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ≠ 0 := by
    intro h
    apply hδ₀
    apply σ.injective
    simpa using h
  have hf : 0 < Ground.fpDimension C X :=
    lt_of_lt_of_le zero_lt_one (Ground.one_le_fpDimension C X (Simple.not_isZero X))
  have hnum := PropertyF.trace_bound_of_overlap
    (t := ‖galoisActualBraidTrace C X p σ t u‖)
    (d := ‖σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))‖)
    (f := Ground.fpDimension C X) (m := t + 2) (norm_ne_zero_iff.mpr hδ) hf
  have hres : ‖galoisActualBraidTrace C X p σ t u‖ ≤
      |‖σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))‖| *
        Ground.fpDimension C X ^ ((t + 2) - 1) := by
    apply hnum
    intro k
    have h := hbound (overlapIndex t k) (overlapProduct X t u k)
      (galois_overlapProduct_unitary X t σ r size T hsmul hunit u hu k)
    have hexp : overlapIndex t k + 2 = (k + 1) * ((t + 2) - 1) + 1 := by
      rw [overlapIndex_formula]
      have hh : (t + 2) - 1 = t + 1 := by omega
      rw [hh]
      ring
    rw [hexp] at h
    have hr := congrArg σ (hrec k)
    simp only [map_mul, map_pow] at hr
    change galoisActualBraidTrace C X p σ (overlapIndex t k) (overlapProduct X t u k) *
      σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        galoisActualBraidTrace C X p σ t u ^ (k + 1) at hr
    calc
      ‖galoisActualBraidTrace C X p σ t u‖ ^ (k + 1) =
          ‖galoisActualBraidTrace C X p σ t u ^ (k + 1)‖ := (norm_pow _ _).symm
      _ = ‖galoisActualBraidTrace C X p σ (overlapIndex t k) (overlapProduct X t u k) *
          σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k‖ := congrArg norm hr.symm
      _ = ‖galoisActualBraidTrace C X p σ (overlapIndex t k) (overlapProduct X t u k)‖ *
          ‖σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))‖ ^ k := by rw [norm_mul, norm_pow]
      _ ≤ |‖σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))‖| ^ k *
          Ground.fpDimension C X ^ ((k + 1) * ((t + 2) - 1) + 1) := by
        simpa only [abs_of_nonneg (norm_nonneg _), mul_comm] using
          mul_le_mul_of_nonneg_right h
            (pow_nonneg (norm_nonneg (σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))))) k)
  simpa [abs_of_nonneg (norm_nonneg _)] using hres

end PropertyF.Ground.Calculus
