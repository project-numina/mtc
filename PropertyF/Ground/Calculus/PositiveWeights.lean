module
public import PropertyF.Ground.Calculus.ThreeRigidity
public import PropertyF.Ground.Calculus.BraidWeights
public import PropertyF.Ground.Calculus.OverlapCoherence

/-! Construction of real nonzero braid-block trace weights from dimensions. -/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u

/-- Real Galois conjugates of positive simple dimensions yield nonzero real
weights in every retained actual braid block, even if their signs differ. -/
theorem exists_galois_braid_trace_weights
    (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n)) (p : PivotalStructure (C := C.Obj))
    (original qdim : Fin (Ground.rank C) → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < original i)
    (htransport : ∀ i, σ (original i : ℂ) = (qdim i : ℂ))
    (hdim : ∀ i, pivotalDimension C p (Ground.simples C i) = (qdim i : ℂ)) :
    ∃ (r : ℕ) (size : Fin r → ℕ)
      (b : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, size⟩)
      (w : Fin r → ℝ),
      (∀ i, 0 < size i) ∧
      IsUnitaryBraidPresentation b ∧
      (∀ i, w i ≠ 0) ∧
      IsTracePresentation C p b w := by
  classical
  obtain ⟨r, size, b, mult, hsize, hunit, hret, _, htrace⟩ :=
    exists_unitary_braid_trace_blocks C X n hfinite p (groundUnitScalarEquiv C)
  let w : Fin r → ℝ := fun j => ∑ i, (mult i j : ℝ) * qdim i
  refine ⟨r, size, b, w, hsize, hunit, ?_, ?_⟩
  · intro j
    have hn := transported_weight_ne_zero (fun i => mult i j) original σ hpos (hret j)
    simp only [htransport, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum] at hn
    exact_mod_cast hn
  · intro z
    simp only [pivotalDimension, ← groundUnitScalarEquiv_apply] at hdim
    rw [actualBraidTrace, htrace]
    simp only [Blocks.trace, w, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, hdim]

/-- Categorical three-strand rigidity from real Galois dimension data and
one intrinsic overlap trace identity. All matrix blocks and weights are
constructed from the actual finite braid images. -/
theorem actual_rigidity_of_overlap_and_galois_dimensions
    (C : BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : PivotalStructure (C := C.Obj))
    (original qdim : Fin (Ground.rank C) → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < original i)
    (htransport : ∀ i, σ (original i : ℂ) = (qdim i : ℂ))
    (hqdim : ∀ i, pivotalDimension C p (Ground.simples C i) = (qdim i : ℂ))
    (d f : ℝ) (hd : d ≠ 0) (hf : 0 < f)
    (hdim : pivotalDimension C p X = (d : ℂ))
    (hfp : Ground.fpDimension C X = f)
    (hS : scalarTrace p (groundUnitScalarEquiv C) (selfMonodromy X) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X)
    (hrec : ∀ u : braidAlgebra X 1, HasOverlapTracePower C p u) : f = |d| := by
  classical
  choose r size b w hsize he hw htrace using fun n =>
    exists_galois_braid_trace_weights C X n (hfinite n) p original qdim σ hpos htransport hqdim
  apply actual_three_strand_rigidity_of_trace_bound C p (b 1) (he 1)
    (hw 1) hd hf hdim hS hfinite (htrace 1)
  intro z hz
  have h := sharp_trace_bound_for_presentations_of_overlap_identity C X p 1 r size b hsize he z hz (hrec z)
  simpa [hdim, hfp, Complex.norm_real, Real.norm_eq_abs] using h

end PropertyF.Ground.Calculus
