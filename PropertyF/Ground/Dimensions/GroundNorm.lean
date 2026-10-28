module
public import Mathlib.Tactic
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import PropertyF.Ground.Dimensions.Trace
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
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

/-- Inverting a scalar multiple of an isomorphism inverts the scalar. -/
theorem iso_inv_eq_inv_smul {X Y : C} {j k : X ≅ Y} {c : ℂ} (hc : c ≠ 0)
    (h : k.hom = c • j.hom) : k.inv = c⁻¹ • j.inv := by
  apply (cancel_mono k.hom).1
  simp only [Linear.smul_comp, ← Linear.comp_smul, Iso.inv_hom_id]
  rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul, Iso.inv_hom_id]

/-- Two isomorphisms from a simple object differ by a nonzero scalar and their inverses
by its inverse. -/
theorem isomorphisms_scalar [HasKernels C] {X Y : C} [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (j k : X ≅ Y) : ∃ c : ℂ, c ≠ 0 ∧ k.hom = c • j.hom ∧
    k.inv = c⁻¹ • j.inv := by
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (k.hom ≫ j.inv)
  have hhom : k.hom = c • j.hom := (cancel_mono j.inv).1 (by
    simpa only [Linear.smul_comp, Iso.hom_inv_id] using hc.symm)
  have hc0 : c ≠ 0 := fun h ↦
    mono_ne_zero_of_id_ne_zero k.hom (id_nonzero X) (by simpa [h] using hhom)
  exact ⟨c, hc0, hhom, iso_inv_eq_inv_smul hc0 hhom⟩
end SimpleIsomorphisms

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [Linear ℂ C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The product of the two quantum traces on a simple object does not depend
on the chosen double-dual isomorphism. -/
theorem squaredNorm_independent {X : C} [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (j k : X ≅ (Xᘁ)ᘁ) :
    scalar (rightQuantumTrace j) * scalar (leftQuantumTrace j) =
      scalar (rightQuantumTrace k) * scalar (leftQuantumTrace k) := by
  obtain ⟨c, hc, hhom, hinv⟩ := isomorphisms_scalar j k
  have hr : rightQuantumTrace k = c • rightQuantumTrace j :=
    rightQuantumTrace_smul_hom hhom
  have hl : leftQuantumTrace k = c⁻¹ • leftQuantumTrace j := by
    apply End.homEquiv.injective
    simp [leftQuantumTrace, hinv, tensorHom_def]
  rw [hr, hl, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  field_simp

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- For every simple object of a genuine braided fusion category, the
intrinsic squared norm in the target is independent of the chosen double-dual
isomorphism. -/
theorem target_squaredNorm_choice_independent
    {X : C.Obj} [Simple X] (j : X ≅ ((Xᘁ)ᘁ)) :
    squaredNorm C X =
      unitScalar C (rightQuantumTrace j) * unitScalar C (leftQuantumTrace j) := by
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  simpa only [squaredNorm, Ground.unitScalar_eq_equiv] using
    squaredNorm_independent (Ground.unitScalarEquiv C) (doubleDualIso C X) j

/-- With any spherical structure the target norm of a simple object is its
categorical dimension squared. -/
theorem target_squaredNorm_eq_dimension_sq
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (X : C.Obj) [Simple X] :
    squaredNorm C X =
      (unitScalar C (rightQuantumTrace (p.iso X))) ^ 2 := by
  rw [target_squaredNorm_choice_independent C (p.iso X),
    ← spherical_quantumTraces_eq p hp X, pow_two]

/-- The target's intrinsic global dimension is the sum of squared spherical
simple dimensions, for any spherical structure. -/
theorem target_globalDimension_eq_sum_squares
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) :
    globalDimension C = ∑ i : Fin (rank C),
      (unitScalar C (rightQuantumTrace (p.iso (simples C i)))) ^ 2 :=
  Finset.sum_congr rfl fun i _ ↦
    let : Simple (simples C i) := simples_simple C i
    target_squaredNorm_eq_dimension_sq C p hp (simples C i)

/-- Intrinsic squared norms are invariant under simple-object isomorphism,
without assuming a pivotal or spherical structure. -/
theorem target_squaredNorm_iso
    {X Y : C.Obj} [Simple X] [Simple Y] (e : X ≅ Y) :
    squaredNorm C X = squaredNorm C Y := by
  let j := doubleDualIso C X
  let k : Y ≅ (Yᘁ)ᘁ := e.symm ≪≫ j ≪≫ rightDualIsoMap (rightDualIsoMap e)
  have hnat : e.hom ≫ k.hom = j.hom ≫ (e.homᘁ)ᘁ := by
    simp [k, rightDualIsoMap]
  have h := quantumTraces_iso e hnat
  rw [target_squaredNorm_choice_independent C j,
      target_squaredNorm_choice_independent C k, h.1, h.2]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The global inequality follows from the simple-object estimates; this
separates the sum-of-squares argument from the remaining ENO estimate. -/
theorem target_globalDimension_le_of_simple_bounds
    {d : Fin (rank C) → ℝ}
    (hbound : ∀ i, |d i| ≤ fpSimple C i) :
    ∑ i, (d i) ^ 2 ≤ globalFPDimension C :=
  Finset.sum_le_sum fun i _ => sq_le_sq' (abs_le.mp (hbound i)).1 (abs_le.mp (hbound i)).2

/-- If each real simple dimension is bounded by its FP dimension, equality of
the global sums is equivalent to saturation at every simple. -/
theorem global_sum_squares_eq_iff
    {d : Fin (rank C) → ℝ}
    (hbound : ∀ i, |d i| ≤ fpSimple C i) :
    (∑ i, (d i) ^ 2) = globalFPDimension C ↔
      ∀ i, |d i| = fpSimple C i := by
  rw [globalFPDimension, Finset.sum_eq_sum_iff_of_le
    (fun i _ => sq_le_sq' (abs_le.mp (hbound i)).1 (abs_le.mp (hbound i)).2)]
  constructor
  · intro heq i
    apply (sq_eq_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hbound i))).mp
    simpa only [sq_abs] using heq i (Finset.mem_univ i)
  · intro heq i _
    rw [← heq i, sq_abs]

/-- A pseudo-unitary global dimension saturates every FP bound when the
intrinsic norms are the squared norms of the given dimensions. -/
theorem norm_saturation_of_pseudoUnitary {d : Fin (rank C) → ℂ}
    (hbound : ∀ i, ‖d i‖ ≤ fpSimple C i)
    (hnorm : ∀ i, squaredNorm C (simples C i) = ((‖d i‖ ^ 2 : ℝ) : ℂ))
    (hpu : PseudoUnitary C) : ∀ i, ‖d i‖ = fpSimple C i := by
  have hb : ∀ i, |‖d i‖| ≤ fpSimple C i := fun i ↦ by
    simpa only [abs_of_nonneg (norm_nonneg _)] using hbound i
  have hg : (∑ i, ‖d i‖ ^ 2) = globalFPDimension C := by
    apply Complex.ofReal_injective
    simpa only [PseudoUnitary, globalDimension, hnorm, ← Complex.ofReal_sum] using hpu
  intro i
  simpa only [abs_of_nonneg (norm_nonneg _)] using
    (global_sum_squares_eq_iff C hb).1 hg i

/-- If some simple has real dimension one, the global sum is at least one. -/
theorem global_sum_squares_one_le {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (h : ∃ i, d i = 1) : 1 ≤ ∑ i, (d i) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := h
  simpa [hi] using
    (Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i))

end PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- Dualizing a double-dual component twice exchanges its left and right
quantum traces. -/
theorem leftQuantumTrace_dual_component {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] {X : C} (j : X ≅ (Xᘁ)ᘁ) :
    leftQuantumTrace (rightDualIsoMap j).symm = rightQuantumTrace j := by
  rw [leftQuantumTrace_eq_rightDual]
  exact (rightQuantumTrace_iso (j := j) (k := rightDualIsoMap (rightDualIsoMap j)) j (by rfl)).symm

/-- The intrinsic squared norm is invariant under right duality, without any
pivotal or spherical structure. -/
theorem target_squaredNorm_rightDual
    (X : C.Obj) [Simple X] : squaredNorm C (Xᘁ) = squaredNorm C X := by
  let : Simple (Xᘁ) := simple_rightDual C X
  let j := doubleDualIso C X
  rw [target_squaredNorm_choice_independent C (rightDualIsoMap j).symm,
    target_squaredNorm_choice_independent C j, ← leftQuantumTrace_eq_rightDual j,
    leftQuantumTrace_dual_component, mul_comm]

end PropertyF.Ground.Dimensions

end
