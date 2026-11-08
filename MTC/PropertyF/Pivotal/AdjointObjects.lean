module
public import MTC.Center.Normalization.AdjointDegrees
public import MTC.Fusion.UnitPower
public import MTC.PropertyF.Pivotal.Statement

/-! # Actual objects in the adjoint tensor closure

This gives one categorical direction of the identification of fusion labels
with the adjoint subcategory; the reverse direction is a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MTC.Fusion MTC.Center.Braid MTC.Center.Normalization
namespace MTC.PropertyF.Pivotal
set_option linter.style.haveILetI false
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The categorical tensor, dual, finite-sum and retract closure of the
objects `S ⊗ S*` for simple objects `S`. -/
inductive AdjointGenerated : C.Obj → Prop
  | unit : AdjointGenerated (𝟙_ C.Obj)
  | seed (S : C.Obj) [Simple S] : AdjointGenerated (S ⊗ (ᘁS))
  | tensor {X Y} : AdjointGenerated X → AdjointGenerated Y → AdjointGenerated (X ⊗ Y)
  | dual {X} : AdjointGenerated X → AdjointGenerated (ᘁX)
  | sum {n : ℕ} (V : Fin n → C.Obj) : (∀ i, AdjointGenerated (V i)) → AdjointGenerated (⨁ V)
  | retract {X Y} : AdjointGenerated Y → Retract X Y → AdjointGenerated X

/-- The labels whose actual representatives lie in the categorical closure. -/
def adjointGeneratedLabels : Finset (Fin (rank C)) := by
  classical
  exact Finset.univ.filter (fun i ↦ AdjointGenerated C (simples C i))

theorem mem_adjointGeneratedLabels (i : Fin (rank C)) :
    i ∈ adjointGeneratedLabels C ↔ AdjointGenerated C (simples C i) := by
  classical
  simp [adjointGeneratedLabels]

/-- Generated simple labels form a fusion subring. -/
theorem adjointGeneratedLabels_fusionSubring :
    IsFusionSubring C (adjointGeneratedLabels C) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    apply (mem_adjointGeneratedLabels C _).2
    exact .retract (.dual ((mem_adjointGeneratedLabels C i).1 hi))
      (Retract.ofIso (dualIndex_iso i).some.symm)
  · intro i hi j hj k hk
    apply (mem_adjointGeneratedLabels C _).2
    exact .retract (.tensor ((mem_adjointGeneratedLabels C i).1 hi)
      ((mem_adjointGeneratedLabels C j).1 hj)) (fusionCoeff_retract hk).some
  · apply (mem_adjointGeneratedLabels C _).2
    exact .retract .unit (Retract.ofIso (unitIndex_iso C).some)

/-- Each adjoint seed occurs in the actual categorical adjoint closure. -/
theorem adjointSeed_generated {k : Fin (rank C)} (hk : AdjointSeed C k) :
    AdjointGenerated C (simples C k) := by
  obtain ⟨i, hi⟩ := hk
  letI : Simple (simples C i) := simples_simple C i
  have hr := (fusionCoeff_retract hi).some
  let e : simples C i ⊗ simples C (dualIndex C i) ≅
      simples C i ⊗ ᘁ(simples C i) := Iso.refl _ ⊗ᵢ (dualIndex_iso i).some.symm
  exact .retract (.seed (simples C i)) (hr.trans (Retract.ofIso e))

/-- Every label in the fusion-generated adjoint subring denotes a simple
object in the actual adjoint tensor closure. -/
theorem adjointLabel_generated {i : Fin (rank C)} (hi : IsAdjointLabel C i) :
    AdjointGenerated C (simples C i) := by
  apply (mem_adjointGeneratedLabels C i).1
  exact hi (adjointGeneratedLabels C) (adjointGeneratedLabels_fusionSubring C)
    (fun _ hk ↦ (mem_adjointGeneratedLabels C _).2 (adjointSeed_generated C hk))

/-- The manuscript's positivity hypothesis on actual simple objects in the
adjoint closure implies the label-level positivity used by the normalization
and centre reductions. -/
theorem positiveOnTransparentAdjoint_of_categorical
    (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj))
    (h : ∀ (X : C.Obj) [Simple X], MTC.Center.Transparent X →
      AdjointGenerated C X → ∃ r : ℝ, 0 < r ∧
        MTC.CategoryTheory.Dimensions.pivotalDimension C p X = (r : ℂ)) :
    PositiveOnTransparentAdjoint C p := by
  intro i hi hadj
  letI : Simple (simples C i) := simples_simple C i
  exact h (simples C i) hi (adjointLabel_generated C hadj)

end MTC.PropertyF.Pivotal
end
