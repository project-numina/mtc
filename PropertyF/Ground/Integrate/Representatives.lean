module
public import PropertyF.Ground.Fusion.Simples

/-! Reindexing finite complete lists of simple objects. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace PropertyF.Ground
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Any finite list of pairwise nonisomorphic simples that covers the chosen
simples is a reindexing of the chosen list. -/
theorem simple_presentation_equiv {n : ℕ} (S : Fin n → C.Obj)
    (hSimple : ∀ i, Simple (S i))
    (hInjective : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hCover : ∀ j, ∃ i, Nonempty (S i ≅ simples C j)) :
    ∃ e : Fin n ≃ Fin (rank C), ∀ i, Nonempty (S i ≅ simples C (e i)) := by
  classical
  choose f hf using fun (i : Fin n) ↦ by
    letI := hSimple i
    exact exists_simple_iso C (S i)
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro i j hij
    obtain ⟨ei⟩ := hf i
    obtain ⟨ej⟩ := hf j
    exact hInjective i j ⟨ei ≪≫ eqToIso (congrArg (simples C) hij) ≪≫ ej.symm⟩
  · intro j
    obtain ⟨i, ⟨e⟩⟩ := hCover j
    obtain ⟨ei⟩ := hf i
    exact ⟨i, simples_injective C ⟨ei.symm ≪≫ e⟩⟩


end PropertyF.Ground
