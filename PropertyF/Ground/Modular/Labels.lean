module
public import PropertyF.Ground.Integrate.Representatives

/-! Simple labels under equivalences of genuine fusion categories. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.Modular
universe v u

/-- An equivalence transports the chosen simple labels bijectively, with an
actual isomorphism between each transported representative and its new label. -/
theorem simpleLabels_equiv (C D : Ground.BraidedFusionCategory.{v,u})
    (E : C.Obj ≌ D.Obj) : ∃ e : Fin (rank C) ≃ Fin (rank D),
    ∀ i, Nonempty (E.functor.obj (simples C i) ≅ simples D (e i)) := by
  classical
  let F := E.functor
  let S : Fin (rank C) → D.Obj := fun i => F.obj (simples C i)
  apply simple_presentation_equiv D S
  · intro i
    let _ : Simple (simples C i) := simples_simple C i
    exact simple_obj F (simples C i)
  · intro i j ⟨e⟩
    apply simples_injective C i j
    exact ⟨F.preimageIso e⟩
  · intro j
    let Y := simples D j
    let X := F.objPreimage Y
    have e := F.objObjPreimageIso Y
    let _ : Simple Y := simples_simple D j
    let _ : Simple (F.obj X) := Simple.of_iso e
    let _ : Simple X := Functor.simple_of_simple_obj F X
    obtain ⟨i, ⟨ei⟩⟩ := exists_simple_iso C X
    exact ⟨i, ⟨F.mapIso ei.symm ≪≫ e⟩⟩

end PropertyF.Ground.Modular
