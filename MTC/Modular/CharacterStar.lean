module
public import MTC.Modular.Verlinde
public import MTC.PropertyF.Reduction.CharacterReality

open MTC.Algebra

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided

/-!
# Duality and complex conjugation of fusion characters

Frobenius reciprocity makes each fusion matrix adjoint to its dual-label
matrix. A finite inner-product calculation then shows that any normalized
character sends dual labels to conjugate complex numbers. Applied to categorical
S columns, this yields the usual dual-conjugation law when dimensions are real.
-/
open scoped BigOperators
@[expose] public noncomputable section
namespace MTC.Modular

variable (C : MTC.Fusion.BraidedFusionCategory) (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj))

local notation "Sₚ" => categoricalS C p
local notation "dₚ" => simpleDimension C p

/-- Each normalized S-matrix column defines a fusion character. -/
def categoricalSCharacter (j : Fin (rank C)) : Character ⟨unitIndex C, fusionCoeff C⟩ where
  value := normalizedSColumn C p j
  unit_eq := by
    change Sₚ (unitIndex C) j / dₚ j = 1
    rw [categoricalS_symmetric C p, categoricalS_unit]
    exact div_self (simpleDimension_ne_zero C p j)
  mul_eq i k := categoricalS_verlinde C p i k j

/-- The simple pivotal dimensions are fixed by complex conjugation. -/
abbrev HasRealSimpleDimensions : Prop :=
  ∀ j, starRingEnd ℂ (dₚ j) = dₚ j

variable (hreal : HasRealSimpleDimensions C p)

include hreal in
/-- With real simple dimensions, dualizing a label conjugates the corresponding
categorical S entry. No categorical dual-trace identity is needed. -/
theorem categoricalS_dual_conj (i j : Fin (rank C)) :
    Sₚ (MTC.Fusion.dualIndex C i) j = starRingEnd ℂ (Sₚ i j) :=
  (div_left_inj' (simpleDimension_ne_zero C p j)).mp (by
    simpa only [categoricalSCharacter, normalizedSColumn, ← starRingEnd_apply, map_div₀, hreal j] using
      MTC.PropertyF.Reduction.fusion_character_dual_eq_conj (i₀ := unitIndex C)
        (fun a b c ↦ (MTC.Fusion.fusionCoeff_dual_symmetry C a b c).symm)
        (by simp [(categoricalSCharacter C p j).unit_eq]) (categoricalSCharacter C p j).mul_eq i)

include hreal in
/-- Real pivotal simple dimensions are invariant under dual labels. -/
theorem simpleDimension_dual (i : Fin (rank C)) :
    dₚ (MTC.Fusion.dualIndex C i) = dₚ i := by
  simpa only [categoricalS_unit, hreal i] using
    categoricalS_dual_conj C p hreal i (unitIndex C)

end MTC.Modular
