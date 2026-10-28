module
public import PropertyF.Ground.Fusion.Simples

/-! # Simple-object representatives

A finite complete list of pairwise nonisomorphic simple objects is equivalent
to the chosen list of representatives. -/

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
    exact hInjective i j <| (hf i).elim fun ei ↦
      (hf j).map fun ej ↦ ei ≪≫ eqToIso (congrArg (simples C) hij) ≪≫ ej.symm
  · intro j
    obtain ⟨i, e⟩ := hCover j
    exact ⟨i, simples_injective C ((hf i).elim fun ei ↦ e.map fun e ↦ ei.symm ≪≫ e)⟩

end PropertyF.Ground
