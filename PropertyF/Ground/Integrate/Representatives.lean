module
public import PropertyF.Ground.Fusion.Simples

/-! # Simple-object representatives

Two mutually covering families of pairwise nonisomorphic objects have
equivalent index types. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace PropertyF.Ground
universe v u
variable {C : Type u} [Category.{v} C] {ι κ : Type*}

/-- Two complete, pairwise nonisomorphic families of objects have equivalent indices. -/
theorem representatives_equiv (S : ι → C) (T : κ → C)
    (hS : ∀ i j, Nonempty (S i ≅ S j) → i = j) (hT : ∀ i j, Nonempty (T i ≅ T j) → i = j)
    (hST : ∀ i, ∃ j, Nonempty (S i ≅ T j)) (hTS : ∀ j, ∃ i, Nonempty (S i ≅ T j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (S i ≅ T (e i)) := by
  classical
  choose f hf using hST
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro i j hij
    exact hS i j <| (hf i).elim fun ei ↦
      (hf j).map fun ej ↦ ei ≪≫ eqToIso (congrArg T hij) ≪≫ ej.symm
  · intro j
    obtain ⟨i, e⟩ := hTS j
    exact ⟨i, hT _ _ ((hf i).elim fun ei ↦ e.map fun e ↦ ei.symm ≪≫ e)⟩

end PropertyF.Ground
