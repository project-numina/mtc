module
public import PropertyF.Ground.Fusion.FunctorDimension
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! The global FP dimension of a full fusion subcategory is bounded by that of
its ambient category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- A full faithful linear functor between semisimple categories sends simples
to simples, because their endomorphism spaces stay one-dimensional. -/
theorem simple_functor_obj (C D : BraidedFusionCategory.{v,u})
    (F : C.Obj ⥤ D.Obj) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
    (i : Fin (rank C)) : Simple (F.obj (simples C i)) := by
  apply simple_of_finrank_end_eq_one D
  let e := LinearEquiv.ofBijective (F.mapLinearMap ℂ :
    (simples C i ⟶ simples C i) →ₗ[ℂ] _) ⟨F.map_injective, F.map_surjective⟩
  rw [← e.finrank_eq, finrank_simples_hom]
  simp

/-- The simple objects of a full fusion subcategory inject into the ambient
simple labels. -/
theorem simple_labels_inclusion (C D : BraidedFusionCategory.{v,u})
    (F : C.Obj ⥤ D.Obj) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful] :
    ∃ e : Fin (rank C) ↪ Fin (rank D),
      ∀ i, Nonempty (F.obj (simples C i) ≅ simples D (e i)) := by
  classical
  have h : ∀ i, ∃ j, Nonempty (F.obj (simples C i) ≅ simples D j) := by
    intro i
    letI := simple_functor_obj C D F i
    exact exists_simple_iso D _
  let e : Fin (rank C) → Fin (rank D) := fun i => Classical.choose (h i)
  have he : ∀ i, Nonempty (F.obj (simples C i) ≅ simples D (e i)) :=
    fun i => Classical.choose_spec (h i)
  have hinj : Function.Injective e := by
    intro i j hij
    obtain ⟨a⟩ := he i
    obtain ⟨b⟩ := he j
    have b' : F.obj (simples C j) ≅ simples D (e i) := by simpa [hij] using b
    exact simples_injective C i j ⟨F.preimageIso (a ≪≫ b'.symm)⟩
  exact ⟨⟨e, hinj⟩, he⟩

/-- A full faithful linear tensor functor cannot increase global FP dimension
when passing to its source. -/
theorem globalFPDimension_le_of_full_functor (C D : BraidedFusionCategory.{v,u})
    (F : C.Obj ⥤ D.Obj) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful] [F.Monoidal] :
    globalFPDimension C ≤ globalFPDimension D := by
  classical
  obtain ⟨e, he⟩ := simple_labels_inclusion C D F
  have hdim (i : Fin (rank C)) : fpSimple C i = fpSimple D (e i) := by
    obtain ⟨a⟩ := he i
    calc
      _ = fpDimension C (simples C i) := (fpDimension_simple C i).symm
      _ = fpDimension D (F.obj (simples C i)) := (fpDimension_functor C D F _).symm
      _ = fpDimension D (simples D (e i)) := fpDimension_iso D a
      _ = _ := fpDimension_simple D _
  unfold globalFPDimension
  calc
    _ = ∑ i, fpSimple D (e i) ^ 2 := by simp only [hdim]
    _ = ∑ j ∈ Finset.univ.image e, fpSimple D j ^ 2 := by
      rw [Finset.sum_image]
      intro i _ j _ h
      exact e.injective h
    _ ≤ ∑ j, fpSimple D j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)

end PropertyF.Ground
