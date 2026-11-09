module
public import MTC.Modular.CharacterStar
public import MTC.Fusion.Agreement

/-!
# Frobenius–Perron column for a pivotal category

The normalized categorical S columns classify fusion characters whenever the
categorical S matrix is invertible. This section does not assume that the
pivotal structure is spherical or that its dimensions are positive.
-/

@[expose] public noncomputable section
open MTC.Fusion MTC.Modular
open scoped BigOperators
namespace MTC.PropertyF.Pivotal

universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj))

/-- Frobenius–Perron dimension is a normalized fusion character. -/
def fpFusionCharacter : Character ⟨unitIndex C, fusionCoeff C⟩ where
  value i := (fpSimple C i : ℂ)
  unit_eq := by simp [fpSimple_unit]
  mul_eq i j := by
    change (fpSimple C i : ℂ) * (fpSimple C j : ℂ) =
      ∑ k, (fusionCoeff C i j k : ℂ) * (fpSimple C k : ℂ)
    exact_mod_cast fpSimple_mul C i j

/-- Invertibility of the categorical S matrix gives a unique simple label
whose normalized S column is the Frobenius–Perron character. -/
theorem existsUnique_fp_column (hdet : (categoricalS C p).det ≠ 0) :
    ∃! j : Fin (rank C), ∀ i,
      categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ) := by
  have hlin : LinearIndependent ℂ (fun j i ↦ normalizedSColumn C p j i) := by
    have h : LinearIndependent ℂ (categoricalS C p).col :=
      Matrix.linearIndependent_cols_of_det_ne_zero hdet
    convert h.units_smul (fun j ↦ (Units.mk0 (simpleDimension C p j)
        (simpleDimension_ne_zero C p j))⁻¹) using 1
    ext j i
    simp [normalizedSColumn, Units.smul_def, div_eq_mul_inv, mul_comm]
  have hbij := characters_bijective ⟨unitIndex C, fusionCoeff C⟩
    (categoricalSCharacter C p) hlin
  have heq : ∀ j, categoricalSCharacter C p j = fpFusionCharacter C ↔
      ∀ i, categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ) := by
    intro j
    constructor
    · intro h i
      have hi := congrFun (congrArg Character.value h) i
      change categoricalS C p i j / simpleDimension C p j = (fpSimple C i : ℂ) at hi
      exact (div_eq_iff (simpleDimension_ne_zero C p j)).mp hi |>.trans (mul_comm _ _)
    · intro h
      apply Character.ext
      funext i
      change categoricalS C p i j / simpleDimension C p j = (fpSimple C i : ℂ)
      rw [h i, mul_comm, mul_div_cancel_right₀ _ (simpleDimension_ne_zero C p j)]
  exact (existsUnique_congr heq).mp (hbij.existsUnique (fpFusionCharacter C))

end MTC.PropertyF.Pivotal
