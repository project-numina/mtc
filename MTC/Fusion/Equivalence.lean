module
public import MTC.PropertyF.Statement

open MTC.Fusion

open MTC.Braided

/-! # Fusion rules of braided fusion categories

An isomorphism of based fusion rings is a bijection of the chosen simple
representatives preserving every tensor product multiplicity. The unit is
necessarily preserved by such a bijection, since it is the ring identity.
The definition does not use braiding or property F.
-/

@[expose] public noncomputable section
open MTC CategoryTheory
namespace MTC.Fusion
universe v u

/-- A multiplicity-preserving bijection between the simple labels. -/
def SameFusionRules (C D : BraidedFusionCategory.{v,u}) : Prop :=
  ∃ e : Fin (rank C) ≃ Fin (rank D),
    ∀ i j k, fusionMatrix C i k j = fusionMatrix D (e i) (e k) (e j)

/-- Every category has the same fusion rules as itself. -/
theorem sameFusionRules_refl (C : BraidedFusionCategory.{v,u}) : SameFusionRules C C :=
  ⟨Equiv.refl _, fun _ _ _ ↦ rfl⟩

/-- The relation of having the same fusion rules is symmetric. -/
theorem sameFusionRules_symm {C D : BraidedFusionCategory.{v,u}}
    (h : SameFusionRules C D) : SameFusionRules D C := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro i j k
  simpa using (he (e.symm i) (e.symm j) (e.symm k)).symm

/-- The relation of having the same fusion rules is transitive. -/
theorem sameFusionRules_trans {C D E : BraidedFusionCategory.{v,u}}
    (hCD : SameFusionRules C D) (hDE : SameFusionRules D E) : SameFusionRules C E := by
  obtain ⟨e, he⟩ := hCD
  obtain ⟨f, hf⟩ := hDE
  exact ⟨e.trans f, fun i j k ↦ (he i j k).trans (hf (e i) (e j) (e k))⟩


/-- Complex-linear braided monoidal equivalence of braided fusion categories. -/
structure BraidedTensorEquivalence (C D : MTC.Fusion.BraidedFusionCategory.{v,u}) where
  equivalence : C.Obj ≌ D.Obj
  [monoidal : equivalence.functor.Monoidal]
  [braided : equivalence.functor.Braided]
  map_smul : ∀ {X Y : C.Obj} (z : ℂ) (f : X ⟶ Y),
    equivalence.functor.map (z • f) = z • equivalence.functor.map f

end MTC.Fusion
