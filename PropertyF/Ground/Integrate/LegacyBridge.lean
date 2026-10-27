module
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Integrate.UnitScalar
public import PropertyF.Ground.Integrate.Conjugacy

/-! Compatibility with the pre-ground categorical bundle. These constructions
are useful for auditing its formerly assumed fields, but declarations that
mention the old bundles are deliberately excluded from the final target cone. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- All fields of the old fusion data follow from the ground fusion category. -/
def legacyFusionData (C : BraidedFusionCategory.{v,u}) : PropertyF.FusionData C.Obj where
  rank := rank C
  simpleObject := simples C
  simple_is_simple := simples_simple C
  simple_injective := simples_injective C
  unitIndex := unitIndex C
  unit_iso := (unitIndex_iso C).some
  hom_finite := IsFusionCategory.hom_finite
  decomposition := simples_decompose C
  fpSimple := fpSimple C
  fp_positive := fpSimple_pos C
  fp_unit := fpSimple_unit C
  fp_character := by
    intro i j
    simpa [fusionCoeff] using fpSimple_mul C i j

/-- The scalar and double-dual choices in the old bundle are constructed. -/
def legacyGlobalDimensionData (C : BraidedFusionCategory.{v,u}) :
    PropertyF.GlobalDimensionData C.Obj (legacyFusionData C) where
  unitScalar := unitScalarEquiv C
  doubleDualIso := fun i => doubleDualIso C (simples C i)

/-- Embed a genuine ground category into the old, choice-carrying interface. -/
def legacyCategory (C : BraidedFusionCategory.{v,u}) : PropertyF.BraidedFusionCategory.{v,u} where
  Obj := C.Obj
  fusion := legacyFusionData C
  dimensionData := legacyGlobalDimensionData C

theorem legacy_globalFPDimension_eq (C : BraidedFusionCategory.{v,u}) :
    (legacyCategory C).fusion.globalFPDimension = globalFPDimension C := rfl

theorem legacy_globalDimension_eq (C : BraidedFusionCategory.{v,u}) :
    (legacyCategory C).globalDimension = globalDimension C := by
  unfold PropertyF.BraidedFusionCategory.globalDimension globalDimension squaredNorm
  apply Finset.sum_congr rfl
  intro i _
  simp only [legacyCategory, legacyGlobalDimensionData, legacyFusionData]
  rw [unitScalar_eq_equiv, unitScalar_eq_equiv]
  rfl

/-- The ground semilinear braided equivalence also witnesses conjugacy in the
legacy category interface. -/
def legacyGaloisConjugate {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ}
    (h : GaloisConjugate C D σ) :
    PropertyF.GaloisConjugate (legacyCategory C) (legacyCategory D) σ where
  equivalence := h.equivalence
  monoidal := h.braided.toMonoidal
  braided := h.braided
  map_smul := h.map_smul

/-- The pseudo-unitary conjugate hypothesis transfers to the legacy bundle. -/
theorem legacy_hasPseudoUnitaryGaloisConjugate (C : BraidedFusionCategory.{v,u})
    (h : HasPseudoUnitaryGaloisConjugate C) :
    PropertyF.HasPseudoUnitaryGaloisConjugate (legacyCategory C) := by
  obtain ⟨D, σ, ⟨E⟩, hD⟩ := h
  refine ⟨legacyCategory D, σ, ⟨legacyGaloisConjugate E⟩, ?_⟩
  unfold PropertyF.PseudoUnitary
  rw [legacy_globalDimension_eq, legacy_globalFPDimension_eq]
  exact hD

end PropertyF.Ground
