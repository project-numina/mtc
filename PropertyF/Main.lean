module
public import PropertyF.Center
public import PropertyF.GaloisRigidity
public import PropertyF.Arithmetic

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF
universe v u

/-- Galois transport preserves global FP dimension because it preserves the
fusion-ring character and permutes simple labels. -/
theorem galois_globalFPDimension (H : StandardInputs.{v,u})
    {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ} (E : GaloisConjugate C D σ) :
    C.fusion.globalFPDimension = D.fusion.globalFPDimension := by
  obtain ⟨e, he⟩ := H.conjugate_labels E
  unfold FusionData.globalFPDimension
  calc
    _ = ∑ i, D.fusion.fpSimple (e i) ^ 2 := by simp_rw [he]
    _ = _ := e.sum_comp (fun j => D.fusion.fpSimple j ^ 2)

/-- Finiteness is invariant under the concrete image equivalences in the
standard Galois-transport input. -/
theorem galois_propertyF (H : StandardInputs.{v,u})
    {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ} (E : GaloisConjugate C D σ)
    (hF : HasPropertyF C.Obj) : HasPropertyF D.Obj := by
  intro Y n
  obtain ⟨X, ⟨e⟩⟩ := H.conjugate_images E Y n
  have := hF X n
  exact Finite.of_equiv (braidImage X n) e.toEquiv.symm

/-- The main contradiction in Theorem 1.1: all global-dimension conjugates of
a pseudo-unitary category with property F coincide. The inputs do not assert
this equality. They give only positivity, the usual upper bound, and standard
centre / spherical / semisimple structures. -/
theorem global_dimension_fixed (C : BraidedFusionCategory.{v,u})
    (I : PseudoUnitaryInputs C) (hF : HasPropertyF C.Obj) (σ : ℂ ≃+* ℂ) :
    σ (C.fusion.globalFPDimension : ℂ) = (C.fusion.globalFPDimension : ℂ) := by
  let δ := C.fusion.globalFPDimension
  have hδ : 0 < δ := lt_of_lt_of_le (I.conjugate_positive 1) (I.conjugate_le 1)
  suffices heq : I.conjugateGlobal σ = δ by rw [I.conjugate_eq, heq]
  by_contra hne
  have hlt : I.conjugateGlobal σ < δ := lt_of_le_of_ne (I.conjugate_le σ) hne
  let M := I.center
  let Y := M.data.galoisLabel σ.symm M.data.unit
  let f := M.dim Y
  let d := (σ (M.data.dimension Y)).re
  have hdreal : σ (f : ℂ) = (d : ℂ) := by
    rw [← M.dimension_real]
    exact (M.conjugate_real σ Y).symm
  have hd : d ≠ 0 := by
    intro hz
    have hzero : σ (M.data.dimension Y) = 0 := by
      rw [← M.conjugate_real σ Y]
      change (d : ℂ) = 0
      simp [hz]
    exact M.data.dimension_ne_zero Y (σ.injective (by simpa using hzero))
  obtain ⟨R⟩ := M.realize σ Y (M.galois_unit_propertyF hF σ.symm)
  have hS : R.model.pairTrace R.model.cSquared = (d : ℂ) * f := by
    rw [R.trace_formula, M.data.galois_unit_column σ.symm Y, map_mul]
    rw [M.dimension_real Y, hdreal]
    simp [Y, f]
  have hrigidity : f = |d| := R.model.rigidity hd (M.positive Y)
    ((R.model.overlap.decomposition 0).weight_ne_zero σ R.positive R.transport R.retained) hS
  have hratio : f * I.conjugateGlobal σ.symm = δ :=
    M.data.positive_dimension_ratio σ.symm hδ (I.conjugate_positive σ.symm)
      (M.positive Y) M.global_square (I.conjugate_eq σ.symm) (M.dimension_real Y)
  have hinverse : σ (I.conjugateGlobal σ.symm : ℂ) = (δ : ℂ) := by
    rw [← I.conjugate_eq σ.symm]
    exact σ.apply_symm_apply _
  exact galois_dimension_contradiction σ hδ (I.conjugate_positive σ) hlt hinverse
    (I.conjugate_eq σ) hdreal hratio (M.at_least_one Y) hrigidity

/-- The pseudo-unitary case of Theorem 1.1, including the arithmetic conclusion. -/
theorem pseudoUnitary_propertyF_implies_weaklyIntegral (C : BraidedFusionCategory.{v,u})
    (I : PseudoUnitaryInputs C) (hF : HasPropertyF C.Obj) :
    WeaklyIntegral C.fusion.globalFPDimension := by
  let A := I.arithmetic
  have hfixed : ∀ σ : A.field ≃ₐ[ℚ] A.field, σ A.element = A.element := by
    intro σ
    obtain ⟨τ, hτ⟩ := A.extend σ
    apply Subtype.ext
    rw [← hτ, A.element_eq, global_dimension_fixed C I hF τ]
  obtain ⟨z, hz⟩ := integer_of_galois_fixed A.integral hfixed
  refine ⟨z, ?_⟩
  have h := congrArg (fun x : A.field => (x : ℂ)) hz
  rw [A.element_eq] at h
  simpa using congrArg Complex.re h

/-- **Theorem 1.1**, with the paper's full hypothesis of a pseudo-unitary Galois
conjugate. `H` is the explicit standard-input and realization ledger in
Axioms.lean. This is a conditional formalization: no global custom axioms and
no `sorry` occur, but the categorical realization bridges in `H` are hypotheses. -/
theorem propertyF_implies_weaklyIntegral (H : StandardInputs.{v,u})
    (C : BraidedFusionCategory.{v,u}) (hPU : HasPseudoUnitaryGaloisConjugate C)
    (hF : HasPropertyF C.Obj) : WeaklyIntegral C.fusion.globalFPDimension := by
  obtain ⟨D, σ, ⟨E⟩, hD⟩ := hPU
  have hDF := galois_propertyF H E hF
  rw [galois_globalFPDimension H E]
  exact pseudoUnitary_propertyF_implies_weaklyIntegral D (H.pseudo D hD) hDF

end PropertyF
