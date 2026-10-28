module
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Fusion.Reciprocity
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! # Nonzero simple dimensions

Simple pivotal dimensions are nonzero, squared norms respect right duals, and positive spherical
dimensions imply pseudo-unitarity.
-/
open scoped BigOperators

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

/-- Simple pivotal dimensions are nonzero, by rigidity, semisimplicity and Schur. -/
theorem pivotalDimension_simple_ne_zero (C : BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    pivotalDimension C p (simples C i) ≠ 0 := by
  simpa [Ground.Modular.simpleDimension, pivotalDimension, unitScalar_eq_equiv] using
    (Ground.Modular.simpleDimension_ne_zero C p i)

end PropertyF.Ground.Dimensions

end

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
    target_squaredNorm_choice_independent C j]
  rw [← leftQuantumTrace_eq_rightDual j, leftQuantumTrace_dual_component]
  exact mul_comm _ _

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every positive pivotal dimension character is the Frobenius–Perron
character. This does not require pseudo-unitarity or sphericality. -/
theorem positive_pivotalDimension_eq_fpSimple
    (p : PivotalStructure (C := C.Obj)) (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) : ∀ i, d i = fpSimple C i := by
  have hunit : d (unitIndex C) = 1 := by
    apply Complex.ofReal_injective
    obtain ⟨e⟩ := unitIndex_iso C
    rw [← hreal, pivotalDimension_iso C p e, pivotalDimension_unit]
    norm_num
  have hchar : ∀ i j, d i * d j = ∑ k, (fusionCoeff C i j k : ℝ) * d k := by
    intro i j
    have h := pivotalDimension_character C p i j
    simp only [hreal] at h
    exact_mod_cast h
  have h := positive_character_unique C d (fpCharacter C) hpos
    (fpCharacter_pos C) hunit (fpCharacter_unit C) hchar (fpCharacter_mul C)
  intro i
  rw [fpSimple_eq_fpCharacter, ← h]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- A positive spherical structure forces pseudo-unitarity. -/
theorem positive_spherical_isPseudoUnitary (C : BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) : PseudoUnitary C := by
  unfold PseudoUnitary globalFPDimension
  rw [target_globalDimension_eq_sum_squares C p hp]
  simp only [← rightTrace_id, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  change pivotalDimension C p (simples C i) ^ 2 = ((fpSimple C i : ℝ) : ℂ) ^ 2
  rw [hreal, positive_pivotalDimension_eq_fpSimple C p d hreal hpos]

end PropertyF.Ground.Dimensions

end
