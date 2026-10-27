module
public import PropertyF.Ground.Calculus.ThreeRigidity
public import PropertyF.Ground.Calculus.BraidWeights
public import PropertyF.Ground.Calculus.OverlapCoherence

/-! Construction of real nonzero braid-block trace weights from dimensions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u

/-- Positive real categorical simple dimensions give strictly positive real
weights for every retained block of the actual braid algebra. -/
theorem exists_positive_braid_trace_weights
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n)) (p : Dimensions.PivotalStructure (C := C.Obj))
    (qdim : Fin (Ground.rank C) → ℝ) (hpos : ∀ i, 0 < qdim i)
    (hdim : ∀ i, Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))) = (qdim i : ℂ)) :
    ∃ (r : ℕ) (size : Fin r → ℕ)
      (b : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (size i)) (Fin (size i)) ℂ)
      (w : Fin r → ℝ),
      (∀ i, 0 < size i) ∧
      (∀ g i, b (groupInImage (braidEndRepresentation X n) g) i ∈
        Matrix.unitaryGroup (Fin (size i)) ℂ) ∧
      (∀ i, 0 < w i) ∧
      ∀ z : braidAlgebra X n, actualBraidTrace C X p n z =
        (PropertyF.Blocks.mk r size).trace w (b z) := by
  classical
  obtain ⟨r, size, b, mult, hsize, hunit, hret, _, htrace⟩ :=
    exists_unitary_braid_trace_blocks C X n hfinite p (Dimensions.groundUnitScalarEquiv C)
  let w : Fin r → ℝ := fun j => ∑ i, (mult i j : ℝ) * qdim i
  refine ⟨r, size, b, w, hsize, hunit, ?_, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := hret j
    exact Finset.sum_pos' (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hpos i).le)
      ⟨i, Finset.mem_univ i, mul_pos (by exact_mod_cast hi) (hpos i)⟩
  · intro z
    rw [actualBraidTrace, htrace]
    simp only [PropertyF.Blocks.trace, w, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, hdim]

/-- Real Galois conjugates of positive simple dimensions yield nonzero real
weights in every retained actual braid block, even if their signs differ. -/
theorem exists_galois_braid_trace_weights
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n)) (p : Dimensions.PivotalStructure (C := C.Obj))
    (original qdim : Fin (Ground.rank C) → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < original i)
    (htransport : ∀ i, σ (original i : ℂ) = (qdim i : ℂ))
    (hdim : ∀ i, Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))) = (qdim i : ℂ)) :
    ∃ (r : ℕ) (size : Fin r → ℕ)
      (b : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (size i)) (Fin (size i)) ℂ)
      (w : Fin r → ℝ),
      (∀ i, 0 < size i) ∧
      (∀ g i, b (groupInImage (braidEndRepresentation X n) g) i ∈
        Matrix.unitaryGroup (Fin (size i)) ℂ) ∧
      (∀ i, w i ≠ 0) ∧
      ∀ z : braidAlgebra X n, actualBraidTrace C X p n z =
        (PropertyF.Blocks.mk r size).trace w (b z) := by
  classical
  obtain ⟨r, size, b, mult, hsize, hunit, hret, _, htrace⟩ :=
    exists_unitary_braid_trace_blocks C X n hfinite p (Dimensions.groundUnitScalarEquiv C)
  let w : Fin r → ℝ := fun j => ∑ i, (mult i j : ℝ) * qdim i
  refine ⟨r, size, b, w, hsize, hunit, ?_, ?_⟩
  · intro j
    have hn := transported_weight_ne_zero (fun i => mult i j) original σ hpos (hret j)
    simp only [htransport, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum] at hn
    exact_mod_cast hn
  · intro z
    rw [actualBraidTrace, htrace]
    simp only [PropertyF.Blocks.trace, w, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, hdim]

/-- Categorical three-strand rigidity from real Galois dimension data and
one intrinsic overlap trace identity. All matrix blocks and weights are
constructed from the actual finite braid images. -/
theorem actual_rigidity_of_overlap_and_galois_dimensions
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (original qdim : Fin (Ground.rank C) → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < original i)
    (htransport : ∀ i, σ (original i : ℂ) = (qdim i : ℂ))
    (hqdim : ∀ i, Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))) = (qdim i : ℂ))
    (d f : ℝ) (hd : d ≠ 0) (hf : 0 < f)
    (hdim : Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) = (d : ℂ))
    (hfp : Ground.fpDimension C X = f)
    (hS : Dimensions.groundUnitScalarEquiv C (p.rightTrace (selfMonodromy X).asHom) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X)
    (hrec : ∀ (u : braidAlgebra X 1) k,
      actualBraidTrace C X p (overlapIndex 1 k) (overlapProduct X 1 u k) *
        (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
          actualBraidTrace C X p 1 u ^ (k + 1)) : f = |d| := by
  classical
  choose r size b w hsize he hw htrace using fun n =>
    exists_galois_braid_trace_weights C X n (hfinite n) p original qdim σ hpos htransport hqdim
  apply actual_three_strand_rigidity_of_trace_bound C X p (r 1) (size 1) (b 1) (he 1)
    (w 1) (hw 1) d f hd hf hdim hS hfinite (htrace 1)
  intro z hz
  have h := sharp_trace_bound_for_presentations_of_overlap_identity C X p 1 r size b hsize he z hz (hrec z)
  simpa [hdim, hfp, Complex.norm_real, Real.norm_eq_abs] using h

set_option backward.isDefEq.respectTransparency false in
/-- Categorical rigidity follows from the precise remaining tensor-power
coherence for three-strand overlaps and real Galois dimension transport. -/
theorem actual_rigidity_of_overlap_coherence
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (original qdim : Fin (Ground.rank C) → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < original i)
    (htransport : ∀ i, σ (original i : ℂ) = (qdim i : ℂ))
    (hqdim : ∀ i, Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))) = (qdim i : ℂ))
    (d f : ℝ) (hd : d ≠ 0) (hf : 0 < f)
    (hdim : Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) = (d : ℂ))
    (hfp : Ground.fpDimension C X = f)
    (hS : Dimensions.groundUnitScalarEquiv C (p.rightTrace (selfMonodromy X).asHom) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X)
    (hcoh : ∀ (u : braidAlgebra X 1) k,
      (isoEndAlgEquiv (overlapPowerIso X 1 k).symm)
        (overlapProduct X 1 u (k + 1) : End (tensorPower X (overlapIndex 1 (k + 1) + 2))) =
      overlapEndProduct (tensorPower X (overlapIndex 1 k + 1)) X (tensorPower X 2)
        (previousOverlapLocal X 1 k u) (u : End (tensorPower X 3))) : f = |d| := by
  apply actual_rigidity_of_overlap_and_galois_dimensions C X p original qdim σ
    hpos htransport hqdim d f hd hf hdim hfp hS hfinite
  intro u
  apply overlap_trace_power_of_step C X p 1 u
  intro k
  exact overlap_trace_step_of_coherence C X p 1 k u (hcoh u k)

end PropertyF.Ground.Calculus
