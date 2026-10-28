module
public import Mathlib.Tactic
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import PropertyF.Ground.Dimensions.Trace
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Fusion.Simples
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Integrate.UnitScalar

/-! # Intrinsic squared norms

Squared norms are independent of duality choices and determine global dimension bounds.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions

universe v u
section SimpleIsomorphisms
variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Inverting a scalar multiple of an isomorphism inverts the scalar. -/
theorem iso_inv_eq_inv_smul {X Y : C} {j k' : X ≅ Y} {c : k} (hc : c ≠ 0)
    (h : k'.hom = c • j.hom) : k'.inv = c⁻¹ • j.inv :=
  (cancel_mono k'.hom).1 <| by
    simp only [Linear.smul_comp, ← Linear.comp_smul, Iso.inv_hom_id]
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul, Iso.inv_hom_id]

/-- Two isomorphisms from a simple object differ by a nonzero scalar. -/
theorem isomorphisms_scalar [IsAlgClosed k] [HasKernels C] {X Y : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (j l : X ≅ Y) :
    ∃ c : k, c ≠ 0 ∧ l.hom = c • j.hom :=
  (endomorphism_simple_eq_smul_id k (l.hom ≫ j.inv)).elim fun c hc ↦
    let hhom : l.hom = c • j.hom := (cancel_mono j.inv).1 (by
      simpa only [Linear.smul_comp, Iso.hom_inv_id] using hc.symm)
    ⟨c, fun h ↦ mono_ne_zero_of_id_ne_zero l.hom (id_nonzero X) (by simpa [h] using hhom), hhom⟩
end SimpleIsomorphisms

variable {k : Type*} [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [Preadditive C] [Linear k C] [RigidCategory C] [HasKernels C]
  [MonoidalPreadditive C] [MonoidalLinear k C]

/-- The product of the two quantum traces on a simple object does not depend
on the chosen double-dual isomorphism. -/
theorem squaredNorm_independent {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (scalar : End (𝟙_ C) ≃ₐ[k] k) (j l : X ≅ (Xᘁ)ᘁ) :
    scalar (rightQuantumTrace j) * scalar (leftQuantumTrace j) =
      scalar (rightQuantumTrace l) * scalar (leftQuantumTrace l) := by
  obtain ⟨c, hc, hhom⟩ := isomorphisms_scalar (k := k) j l
  have hl : leftQuantumTrace l = c⁻¹ • leftQuantumTrace j := by
    apply End.homEquiv.injective
    simp [leftQuantumTrace, iso_inv_eq_inv_smul hc hhom, tensorHom_def]
  rw [rightQuantumTrace_smul_hom hhom, hl, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  field_simp

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] IsFusionCategory.hom_finite
/-- For every simple object of a genuine braided fusion category, the
intrinsic squared norm in the target is independent of the chosen double-dual
isomorphism. -/
theorem target_squaredNorm_choice_independent
    {X : C.Obj} [Simple X] (j : X ≅ ((Xᘁ)ᘁ)) :
    squaredNorm C X =
      unitScalar C (rightQuantumTrace j) * unitScalar C (leftQuantumTrace j) :=
  by simpa only [squaredNorm, Ground.unitScalar_eq_equiv] using
    squaredNorm_independent (Ground.unitScalarEquiv C) (doubleDualIso C X) j

section
variable (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
include hp

/-- With any spherical structure the target norm of a simple object is its
categorical dimension squared. -/
theorem target_squaredNorm_eq_dimension_sq (X : C.Obj) [Simple X] :
    squaredNorm C X =
      (unitScalar C (rightQuantumTrace (p.iso X))) ^ 2 := by
  rw [target_squaredNorm_choice_independent C (p.iso X),
    ← spherical_quantumTraces_eq p hp X, pow_two]

/-- The target's intrinsic global dimension is the sum of squared spherical
simple dimensions, for any spherical structure. -/
theorem target_globalDimension_eq_sum_squares :
    globalDimension C = ∑ i : Fin (rank C),
      (unitScalar C (rightQuantumTrace (p.iso (simples C i)))) ^ 2 :=
  Finset.sum_congr rfl fun i _ ↦
    let : Simple (simples C i) := simples_simple C i
    target_squaredNorm_eq_dimension_sq C p hp (simples C i)

end

/-- Intrinsic squared norms are invariant under object isomorphism. -/
theorem target_squaredNorm_iso {X Y : C.Obj} (e : X ≅ Y) :
    squaredNorm C X = squaredNorm C Y := by
  obtain ⟨hr, hl⟩ := quantumTraces_iso e (j := doubleDualIso C X) (k := doubleDualIso C Y)
    (drinfeldIso_natural e.hom)
  simp only [squaredNorm, hr, hl]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- Pointwise absolute-value bounds imply the corresponding sum-of-squares bound. -/
theorem sum_sq_le_sum_sq_of_abs_le {k : Type*} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]
    {ι : Type*} [Fintype ι] {d f : ι → k}
    (hbound : ∀ i, |d i| ≤ f i) : ∑ i, (d i) ^ 2 ≤ ∑ i, (f i) ^ 2 :=
  Finset.sum_le_sum fun i _ => sq_le_sq' (abs_le.mp (hbound i)).1 (abs_le.mp (hbound i)).2

/-- A sum-of-squares bound is saturated precisely when every term is saturated. -/
theorem sum_sq_eq_sum_sq_iff {k : Type*} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]
    {ι : Type*} [Fintype ι] {d f : ι → k}
    (hbound : ∀ i, |d i| ≤ f i) :
    (∑ i, (d i) ^ 2) = ∑ i, (f i) ^ 2 ↔ ∀ i, |d i| = f i := by
  rw [Finset.sum_eq_sum_iff_of_le
    (fun i _ => sq_le_sq' (abs_le.mp (hbound i)).1 (abs_le.mp (hbound i)).2)]
  constructor
  · intro heq i
    apply (sq_eq_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hbound i))).mp
    simpa only [sq_abs] using heq i (Finset.mem_univ i)
  · intro heq i _
    rw [← heq i, sq_abs]

variable {C} in
/-- A pseudo-unitary global dimension saturates every FP bound when the
intrinsic norms are the squared norms of the given dimensions. -/
theorem norm_saturation_of_pseudoUnitary {d : Fin (rank C) → ℂ}
    (hbound : ∀ i, ‖d i‖ ≤ fpSimple C i)
    (hnorm : ∀ i, squaredNorm C (simples C i) = ((‖d i‖ ^ 2 : ℝ) : ℂ))
    (hpu : PseudoUnitary C) : ∀ i, ‖d i‖ = fpSimple C i := by
  have hg : (∑ i, ‖d i‖ ^ 2) = globalFPDimension C := by
    apply Complex.ofReal_injective
    simpa only [PseudoUnitary, globalDimension, hnorm, ← Complex.ofReal_sum] using hpu
  simpa only [abs_of_nonneg (norm_nonneg _)] using
    (sum_sq_eq_sum_sq_iff (fun i ↦ by
      simpa only [abs_of_nonneg (norm_nonneg _)] using hbound i)).1 hg

/-- If some simple has real dimension one, the global sum is at least one. -/
theorem global_sum_squares_one_le {k : Type*} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]
    {ι : Type*} [Fintype ι] (d : ι → k) (h : ∃ i, d i = 1) : 1 ≤ ∑ i, (d i) ^ 2 :=
  h.elim fun i hi ↦ by
    classical
    simpa [hi] using Finset.single_le_sum (fun j _ ↦ sq_nonneg (d j)) (Finset.mem_univ i)

end PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The intrinsic squared norm is invariant under right duality, without any
pivotal or spherical structure. -/
theorem target_squaredNorm_rightDual
    (X : C.Obj) [Simple X] : squaredNorm C (Xᘁ) = squaredNorm C X := by
  let : Simple (Xᘁ) := simple_rightDual X
  let j := doubleDualIso C X
  rw [target_squaredNorm_choice_independent C (rightDualIsoMap j).symm,
    target_squaredNorm_choice_independent C j, ← leftQuantumTrace_eq_rightDual j,
    leftQuantumTrace_eq_rightDual ((rightDualIsoMap j).symm),
    ← rightQuantumTrace_iso j rfl, mul_comm]

end PropertyF.Ground.Dimensions

end
