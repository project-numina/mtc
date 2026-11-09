module
public import MTC.Braided.Trace.TensorPowerCoherence

/-!
# General pivotal braid trace bound

The overlapping-braid argument works for arbitrary complex pivotal dimensions,
without any sign or nonvanishing hypothesis on the block trace weights.
-/

open MTC.Algebra MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory

@[expose] public noncomputable section
namespace MTC.Braided.Trace
universe v u

/-- The sharp Section 3 estimate for an actual unitary braid-algebra element,
for an arbitrary pivotal structure and any unitary block presentation. -/
theorem pivotal_unitary_trace_bound (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) {X : C.Obj} [Simple X]
    (hfinite : ObjectPropertyF X) {t r : ℕ} {size : Fin r → ℕ}
    (b : BraidBlockPresentation X t size) (hb : IsUnitaryBraidPresentation b)
    (z : braidAlgebra X t) (hz : Blocks.IsUnitary ⟨r, size⟩ (b z)) :
    ‖actualBraidTrace C p z‖ ≤ ‖pivotalDimension C p X‖ *
      MTC.Fusion.fpDimension C X ^ (t + 1) := by
  classical
  choose r' size' e hsize he using fun n => by
    letI : Finite (braidImage X n) := hfinite n
    exact groupImageAlgebra_unitary_blocks (braidEndRepresentation X n)
  have hz' : Blocks.IsUnitary ⟨r' t, size' t⟩ (e t z) := by
    simpa [Blocks.IsUnitary, addLeftBlocksIterStarMap, addLeftBraidAlgebraIter] using!
      Unitary.map_mem (addLeftBlocksIterStarMap X t 0 b (e t) hb (he t)) hz
  exact sharp_trace_bound_of_overlap C p z
    (fun k => braid_trace_unitary_bound_ground C p
      (fun j => Nat.pos_of_ne_zero (hsize _ j).ne) (e _)
      (overlapProduct z k) (overlapProduct_unitary e he hz' k))
    (overlap_trace_power C p z)

end MTC.Braided.Trace
