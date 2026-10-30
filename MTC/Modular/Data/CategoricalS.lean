module
public import MTC.Modular.Data.Basic
public import MTC.Modular.SMatrix

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided

/-!
# Comparison with the categorical S-matrix

The comparison below is conditional: constructing modular data from a category
requires a ribbon twist, nondegeneracy, and proofs of all the data axioms. This
file does not assume that every numerical datum is categorically realized.
-/

@[expose] public noncomputable section
open scoped BigOperators
open MTC MTC.CategoryTheory.Dimensions MTC.Modular

namespace MTC.Modular.Data
universe v u

variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- The labels are the chosen simple representatives and the S-matrix is the
categorical double-braiding trace in the same normalization. This records only
S and the vacuum; it is not a realization certificate for the twist or fusion. -/
def MatchesCategoricalS (d : Data ℂ (rank C)) : Prop :=
  d.vacuum = unitIndex C ∧ d.S = categoricalS C p

/-- Under sphericality, matching S identifies the two global dimensions. -/
theorem globalDimension_eq_categorical (d : Data ℂ (rank C))
    (h : MatchesCategoricalS C p d) (hp : p.IsSpherical) :
    d.globalDimension = MTC.Fusion.globalDimension C := by
  rw [categorical_global_eq_sum_squares C p hp]
  simp only [globalDimension, h.1, h.2, categoricalS_symmetric C p,
    categoricalS_unit C p]

end MTC.Modular.Data
