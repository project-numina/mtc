module
public import MTC.Braided.Trace.ThreeRigidity
public import MTC.Braided.Trace.BraidWeights
public import MTC.Braided.Trace.OverlapCoherence

open MTC.Fusion

open MTC.Braided

/-!
# Nonzero weights for braid traces

Galois transport of positive constituent dimensions gives nonzero braid-block trace
weights. These weights supply the hypotheses of the three-strand rigidity argument.
-/

open MTC.CategoryTheory.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Braided.Trace
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
variable (original qdim : Fin (MTC.Fusion.rank C) → ℝ) (σ : ℂ ≃+* ℂ)
  (hpos : ∀ i, 0 < original i)
  (htransport : ∀ i, σ (original i : ℂ) = (qdim i : ℂ))
  (hqdim : ∀ i, pivotalDimension C p (MTC.Fusion.simples C i) = (qdim i : ℂ))
include hpos htransport hqdim

/-- Real Galois conjugates of positive simple dimensions yield nonzero real
weights in every retained actual braid block, even if their signs differ. -/
theorem exists_galois_braid_trace_weights
    {X : C.Obj} {n : ℕ}
    (hfinite : Finite (braidImage X n)) :
    ∃ (r : ℕ) (size : Fin r → ℕ)
      (b : BraidBlockPresentation X n size)
      (w : Fin r → ℝ),
      (∀ i, 0 < size i) ∧
      IsUnitaryBraidPresentation b ∧
      (∀ i, w i ≠ 0) ∧
      IsTracePresentation C p b w :=
  let ⟨r, size, b, mult, hsize, hunit, hret, _, htrace⟩ :=
    exists_unitary_braid_trace_blocks C p (MTC.unitScalarEquiv C) hfinite
  let w : Fin r → ℝ := fun j => ∑ i, (mult i j : ℝ) * qdim i
  ⟨r, size, b, w, hsize, hunit,
    (fun j => transported_weight_ne_zero (fun i => mult i j) original qdim σ
      hpos htransport (hret j)), fun z => by
      unfold pivotalDimension at hqdim
      simpa [actualBraidTrace, Blocks.trace, w, ← unitScalar_eq_equiv, hqdim] using htrace z⟩

/-- Categorical three-strand rigidity from real Galois dimension data and
one intrinsic overlap trace identity. All matrix blocks and weights are
constructed from the actual finite braid images. -/
theorem actual_rigidity_of_overlap_and_galois_dimensions
    (X : C.Obj) [Simple X]
    (d f : ℝ) (hd : d ≠ 0) (hf : 0 < f)
    (hdim : pivotalDimension C p X = (d : ℂ))
    (hfp : MTC.fpDimension C X = f)
    (hS : scalarTrace p (MTC.unitScalarEquiv C) (selfMonodromy X) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X)
    (hrec : ∀ u : braidAlgebra X 1, HasOverlapTracePower C p u) : f = |d| := by
  classical
  choose r size b w hsize he hw htrace using fun n =>
    exists_galois_braid_trace_weights C p original qdim σ hpos htransport hqdim (hfinite n)
  apply actual_three_strand_rigidity_of_trace_bound C p (b 1) (he 1)
    (hw 1) (htrace 1) ?_ hd hf hdim hS hfinite
  intro z hz
  have hbound := sharp_trace_bound_of_overlap C p z (fun k =>
    braid_trace_unitary_bound_ground C p (hsize _) (b _)
      (overlapProduct z k) (overlapProduct_unitary b he hz k)) (hrec z)
  simpa [hdim, hfp, Complex.norm_real, Real.norm_eq_abs] using hbound

end MTC.Braided.Trace
