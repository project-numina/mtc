module
public import PropertyF.Ground.Calculus.TensorPowerCoherence
public import PropertyF.Ground.Calculus.GaloisRigidity

/-! The sharp categorical and Galois trace bounds and three-strand rigidity. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

/-- Lemma 3.1 for any constructed unitary presentation of the actual braid
algebras of a simple object. -/
theorem sharp_braid_trace_bound
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (t : ℕ)
    (r : ℕ → ℕ) (size : ∀ n, Fin (r n) → ℕ)
    (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (size n i)) (Fin (size n i)) ℂ)
    (hsize : ∀ n i, 0 < size n i)
    (he : ∀ n g i, e n (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (size n i)) ℂ)
    (u : braidAlgebra X t) (hu : ∀ i, e t u i ∈ Matrix.unitaryGroup (Fin (size t i)) ℂ) :
    ‖actualBraidTrace C X p t u‖ ≤
      ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖ *
        Ground.fpDimension C X ^ (t + 1) :=
  sharp_trace_bound_for_presentations_of_overlap_identity C X p t r size e hsize he u hu
    (overlap_trace_power C X p t u)

/-- Lemma 3.1 after arbitrary semilinear Galois transport of the actual braid
algebras. -/
theorem galois_sharp_braid_trace_bound
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
    (u : braidAlgebra X t) (hu : ∀ i, T t u i ∈ Matrix.unitaryGroup (Fin (size t i)) ℂ) :
    ‖galoisActualBraidTrace C X p σ t u‖ ≤
      ‖σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))‖ *
        Ground.fpDimension C X ^ (t + 1) :=
  galois_sharp_trace_bound_of_overlap_identity C X p σ t r size T hsmul hunit hbound u hu
    (overlap_trace_power C X p t u)

/-- The paper's three-strand rigidity conclusion, proved directly in the
original genuine category and with no overlap or block-realization premise. -/
theorem galois_three_strand_rigidity
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ)
    (original conjugate : Fin (Ground.rank C) → ℝ)
    (hpos : ∀ i, 0 < original i)
    (hdims : ∀ i, Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))) = (original i : ℂ))
    (hreal : ∀ i, σ (original i : ℂ) = (conjugate i : ℂ))
    (d f : ℝ) (hd : d ≠ 0) (hf : 0 < f)
    (hdim : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) = (d : ℂ))
    (hfp : Ground.fpDimension C X = f)
    (hS : σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace (selfMonodromy X).asHom)) =
      (d : ℂ) * f)
    (hfinite : ObjectPropertyF X) : f = |d| :=
  galois_rigidity_of_overlap_identity C X p σ original conjugate hpos hdims hreal
    d f hd hf hdim hfp hS hfinite (fun u => overlap_trace_power C X p 1 u)

end PropertyF.Ground.Calculus
