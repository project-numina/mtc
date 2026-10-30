module
public import MTC.Modular.SMatrix

/-!
# Nondegenerate spherical braided fusion categories

This category-level predicate uses an actual spherical pivotal structure and
its categorical double-braiding trace matrix. It is the standard S-matrix
formulation of a modular fusion category, subject to the existing ground
interface's categorical identifications. No connection to an independently
specified numerical modular-data record is asserted.
-/

@[expose] public noncomputable section
open MTC MTC.CategoryTheory.Dimensions MTC.Modular
namespace MTC.PropertyF
universe v u

/-- A spherical pivotal structure with nonzero determinant of its categorical S matrix. -/
def HasNondegenerateSphericalStructure (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ (categoricalS C p).det ≠ 0

/-- An explicit spherical structure and invertible S matrix give the predicate. -/
theorem hasNondegenerateSphericalStructure_of_data (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hs : p.IsSpherical)
    (hS : (categoricalS C p).det ≠ 0) : HasNondegenerateSphericalStructure C :=
  ⟨p, hs, hS⟩

end MTC.PropertyF
