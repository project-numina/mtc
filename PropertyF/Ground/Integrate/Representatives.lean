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
  have hExists : ∀ i, ∃ j, Nonempty (S i ≅ simples C j) := by
    intro i
    let : Simple (S i) := hSimple i
    exact exists_simple_iso C (S i)
  let f : Fin n → Fin (rank C) := fun i => Classical.choose (hExists i)
  have hf : ∀ i, Nonempty (S i ≅ simples C (f i)) :=
    fun i => Classical.choose_spec (hExists i)
  have hinj : Function.Injective f := by
    intro i j hij
    obtain ⟨ei⟩ := hf i
    obtain ⟨ej⟩ := hf j
    apply hInjective i j
    have ej' : S j ≅ simples C (f i) := by simpa only [hij] using ej
    exact ⟨ei ≪≫ ej'.symm⟩
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, ⟨e⟩⟩ := hCover j
    obtain ⟨ei⟩ := hf i
    refine ⟨i, ?_⟩
    exact simples_injective C (f i) j ⟨ei.symm ≪≫ e⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- Any isomorphism-invariant quantity has a presentation-independent sum. -/
theorem sum_simple_presentation {n : ℕ} (S : Fin n → C.Obj)
    (hSimple : ∀ i, Simple (S i))
    (hInjective : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hCover : ∀ j, ∃ i, Nonempty (S i ≅ simples C j))
    {A : Type*} [AddCommMonoid A] (value : C.Obj → A)
    (hValue : ∀ X Y, Simple X → Simple Y → Nonempty (X ≅ Y) → value X = value Y) :
    ∑ i, value (S i) = ∑ j, value (simples C j) := by
  obtain ⟨e, he⟩ := simple_presentation_equiv C S hSimple hInjective hCover
  calc
    _ = ∑ i, value (simples C (e i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hValue _ _ (hSimple i) (simples_simple C (e i)) (he i)
    _ = _ := e.sum_comp (fun j => value (simples C j))

end PropertyF.Ground
