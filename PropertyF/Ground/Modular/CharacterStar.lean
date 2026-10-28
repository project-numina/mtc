module
public import PropertyF.Ground.Modular.Verlinde
public import Mathlib.Analysis.Complex.Norm

/-!
# Duality and complex conjugation of fusion characters

Frobenius reciprocity makes each fusion matrix adjoint to its dual-label
matrix. A finite inner-product calculation then shows that any normalized
character sends dual labels to conjugate complex numbers. Applied to categorical
S columns, this yields the usual dual-conjugation law when dimensions are real.
-/
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (N : FusionRules ι) (dual : ι → ι)
variable (hdual : ∀ i j k, N.coeff i j k = N.coeff (dual i) k j)

omit [DecidableEq ι] in
include hdual in
/-- Fusion duality balances the pairing of two fusion characters. -/
theorem character_inner_balance (χ ψ : Character N) (i : ι) :
    ψ.value i * (∑ j, starRingEnd ℂ (χ.value j) * ψ.value j) =
      starRingEnd ℂ (χ.value (dual i)) *
        (∑ j, starRingEnd ℂ (χ.value j) * ψ.value j) := by
  classical
  let w : ℂ := ∑ j, starRingEnd ℂ (χ.value j) * ψ.value j
  change ψ.value i * w = starRingEnd ℂ (χ.value (dual i)) * w
  calc
    _ = ∑ j, starRingEnd ℂ (χ.value j) * (ψ.value i * ψ.value j) := by
      simp only [w, Finset.mul_sum, mul_left_comm]
    _ = ∑ j, ∑ k, starRingEnd ℂ (χ.value j) * ((N.coeff i j k : ℂ) * ψ.value k) := by
      simp only [ψ.mul_eq, Finset.mul_sum]
    _ = ∑ k, ∑ j, ((N.coeff (dual i) k j : ℂ) * starRingEnd ℂ (χ.value j)) * ψ.value k := by
      rw [Finset.sum_comm]
      simp only [hdual i, mul_comm, mul_assoc]
    _ = ∑ k, starRingEnd ℂ (χ.value (dual i) * χ.value k) * ψ.value k := by
      simp only [χ.mul_eq, map_sum, Finset.sum_mul, map_mul, map_natCast]
    _ = starRingEnd ℂ (χ.value (dual i)) * w := by
      simp only [w, map_mul, Finset.mul_sum, mul_left_comm, mul_assoc]

omit [DecidableEq ι] in
include hdual in
/-- Fusion duality makes every normalized character compatible with conjugation. -/
theorem character_dual_conj (χ : Character N) (i : ι) :
    χ.value (dual i) = starRingEnd ℂ (χ.value i) := by
  classical
  let w : ℂ := ∑ j, starRingEnd ℂ (χ.value j) * χ.value j
  have hw : w ≠ 0 := by
    have hr : 0 < ∑ j, Complex.normSq (χ.value j) :=
      Finset.sum_pos' (fun j _ ↦ Complex.normSq_nonneg _)
        ⟨N.unit, Finset.mem_univ _, by simp [χ.unit_eq]⟩
    have hw' : w = ((∑ j, Complex.normSq (χ.value j) : ℝ) : ℂ) := by
      simp only [w, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
    rw [hw']
    exact_mod_cast ne_of_gt hr
  have h : χ.value i = starRingEnd ℂ (χ.value (dual i)) :=
    mul_right_cancel₀ hw (by simpa [w] using character_inner_balance N dual hdual χ χ i)
  simpa using (congrArg (starRingEnd ℂ) h).symm

/-- Actual fusion coefficients satisfy the adjointness relation. -/
theorem fusionCoeff_dual_adjoint (C : Ground.BraidedFusionCategory) (i j k : Fin (rank C)) :
    fusionCoeff C i j k = fusionCoeff C (Ground.dualIndex C i) k j :=
  (fusionCoeff_comm C i j k).trans <|
    (fusionCoeff_reciprocity_labels C j i k).trans (fusionCoeff_comm C k (Ground.dualIndex C i) j)

variable (C : Ground.BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))

/-- Each normalized S-matrix column defines a fusion character. -/
def categoricalSCharacter (j : Fin (rank C)) : Character ⟨unitIndex C, fusionCoeff C⟩ where
  value i := categoricalS C p i j / simpleDimension C p j
  unit_eq := by
    rw [categoricalS_symmetric C p, categoricalS_unit]
    exact div_self (simpleDimension_ne_zero C p j)
  mul_eq i k := categoricalS_verlinde C p i k j

/-- The simple pivotal dimensions are fixed by complex conjugation. -/
abbrev HasRealSimpleDimensions : Prop :=
  ∀ j, starRingEnd ℂ (simpleDimension C p j) = simpleDimension C p j

variable (hreal : HasRealSimpleDimensions C p)

include hreal in
/-- With real simple dimensions, dualizing a label conjugates the corresponding
categorical S entry. No categorical dual-trace identity is needed. -/
theorem categoricalS_dual_conj (i j : Fin (rank C)) :
    categoricalS C p (Ground.dualIndex C i) j = starRingEnd ℂ (categoricalS C p i j) := by
  let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  let χ : Character rules := categoricalSCharacter C p j
  have hh := character_dual_conj rules (Ground.dualIndex C) (fusionCoeff_dual_adjoint C) χ i
  change categoricalS C p (Ground.dualIndex C i) j / simpleDimension C p j =
    starRingEnd ℂ (categoricalS C p i j / simpleDimension C p j) at hh
  rw [map_div₀, hreal j] at hh
  exact (div_left_inj' (simpleDimension_ne_zero C p j)).mp hh

include hreal in
/-- Real pivotal simple dimensions are invariant under dual labels. -/
theorem simpleDimension_dual (i : Fin (rank C)) :
    simpleDimension C p (Ground.dualIndex C i) = simpleDimension C p i := by
  simpa only [categoricalS_unit, hreal i] using
    categoricalS_dual_conj C p hreal i (unitIndex C)

end PropertyF.Ground.Modular
