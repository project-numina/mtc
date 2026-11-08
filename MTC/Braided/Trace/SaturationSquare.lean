module
public import MTC.Braided.Trace.MonodromyReciprocity

/-! Interface from ordinary tensor-square constituents to trace saturation. -/

open MTC.Algebra MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory

@[expose] public noncomputable section
namespace MTC.Braided.Trace
universe v u

/-- A simple that occurs in the two-strand tensor power admits a nonzero map
to the ordinary tensor square. -/
theorem nonzero_square_hom_of_braid_multiplicity
    (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj)
    (h : 0 < Module.finrank ℂ (Y ⟶ braidTensorPower X 0)) :
    ∃ f : Y ⟶ X ⊗ X, f ≠ 0 := by
  let _ : FiniteDimensional ℂ (Y ⟶ X ⊗ X) := MTC.Fusion.IsFusionCategory.hom_finite _ _
  have he := (CategoryTheory.Linear.homCongr ℂ (Iso.refl Y) (twoPowerIso X)).finrank_eq
  have h' : 0 < Module.finrank ℂ (Y ⟶ X ⊗ X) := by
    rw [← he]
    exact h
  exact Module.finrank_pos_iff_exists_ne_zero.mp h'

/-- Saturation from an ordinary tensor-square phase law, formulated for every
actual simple constituent rather than a chosen list of representatives. -/
theorem saturation_of_square_phase
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    {X : C.Obj} [Simple X] (hfinite : ObjectPropertyF X) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (hphase : ∀ (Y : C.Obj) [Simple Y], (∃ f : Y ⟶ X ⊗ X, f ≠ 0) →
      pivotalDimension C p Y = ξ * star (pivotalDimension C p Y))
    (hmax : ‖scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) /
      pivotalDimension C p X‖ = MTC.Fusion.fpDimension C X) :
    ‖pivotalDimension C p X‖ = MTC.Fusion.fpDimension C X :=
  saturation_of_constituent_phase C p hfinite ξ hξ
    (fun i hi => by
      let _ : Simple (MTC.Fusion.simples C i) := MTC.Fusion.simples_simple C i
      exact hphase (MTC.Fusion.simples C i)
        (nonzero_square_hom_of_braid_multiplicity C X _ hi)) hmax

end MTC.Braided.Trace
