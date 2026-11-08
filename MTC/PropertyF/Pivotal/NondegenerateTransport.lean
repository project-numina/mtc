module
public import MTC.PropertyF.Pivotal.Galois
public import MTC.Modular.FusionTransport

/-! # Nondegeneracy under semilinear braided equivalence -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open CategoryTheory.Functor.Monoidal CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal
open MTC.Fusion MTC.Modular
namespace MTC.PropertyF.Pivotal
set_option linter.style.haveILetI false
universe v u
variable {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ}

/-- A faithful braided functor reflects transparency of objects. -/
theorem transparent_of_braided_functor_image
    (F : C.Obj ⥤ D.Obj) [F.Braided] [F.Faithful]
    (X : C.Obj) (hX : MTC.Center.Transparent (F.obj X)) :
    MTC.Center.Transparent X := by
  intro Y
  apply F.map_injective
  have h := hX (F.obj Y)
  change doubleBraiding (F.obj X) (F.obj Y) = 𝟙 _ at h
  simp only [Functor.map_comp, Functor.map_braiding, Category.assoc]
  simp only [μ_δ_assoc]
  rw [F.map_id]
  -- comparison conjugates the target monodromy
  have h' := congrArg (fun f ↦ (μIso F X Y).inv ≫ f ≫ (μIso F X Y).hom) h
  simpa only [doubleBraiding, Category.assoc, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id, μIso_hom, μIso_inv,
    Functor.map_id, δ_μ] using h'

/-- Semilinear braided Galois equivalences preserve nondegeneracy. -/
theorem isNondegenerate_conjugate (h : GaloisConjugate C D σ)
    (hC : IsNondegenerate C) : IsNondegenerate D := by
  let F := h.equivalence.functor
  letI := h.monoidal
  letI := h.braided
  intro j hj
  letI : Simple (simples D j) := simples_simple D j
  let X := F.objPreimage (simples D j)
  let e := F.objObjPreimageIso (simples D j)
  have hFX : MTC.Center.Transparent (F.obj X) := transparent_of_iso D e hj
  have hX : MTC.Center.Transparent X := transparent_of_braided_functor_image F X hFX
  letI : Simple (F.obj X) := Simple.of_iso e
  letI : Simple X := Functor.simple_of_simple_obj F X
  obtain ⟨i, ⟨ei⟩⟩ := exists_simple_iso C X
  have hi : MTC.Center.Transparent (simples C i) := transparent_of_iso C ei.symm hX
  have hiu := hC i hi
  apply simples_injective D
  have eu : simples C i ≅ 𝟙_ C.Obj := hiu ▸ (unitIndex_iso C).some
  exact ⟨e.symm ≪≫ F.mapIso ei ≪≫ F.mapIso eu ≪≫ (εIso F).symm ≪≫
    (unitIndex_iso D).some.symm⟩

end MTC.PropertyF.Pivotal
end
