module
public import MTC.PropertyF.Statement

/-! # Fusion rules of braided fusion categories

An isomorphism of based fusion rings is a bijection of the chosen simple
representatives preserving every tensor product multiplicity. The unit is
necessarily preserved by such a bijection, since it is the ring identity.
The definition does not use braiding or property F.
-/

@[expose] public noncomputable section
open MTC
namespace MTC.PropertyF
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

end MTC.PropertyF
