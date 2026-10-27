module
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion

/-! Assembly of the actual centre fusion property from induction and averaging. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u

/-- Finite semisimplicity in the ground fusion interface follows from the
right adjoint and the spherical loop-sliding identity. Both assumptions are
still unproved; no centre rigidity is needed for this step. -/
theorem finite_semisimple_of_adjunction_and_loop (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I) :
    ∃ (n : ℕ) (S : Fin n → CategoryTheory.Center C.Obj),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X, ∃ m : Fin n → ℕ,
        Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1))) := by
  classical
  obtain ⟨labels, hs, hc⟩ := finite_simple_labels_of_adjunction_and_loop C p hp hslide hne I adj
  obtain ⟨n, S, hS, hinj, hcover⟩ := simple_representatives_of_finite_cover labels hs hc
  refine ⟨n, S, hS, hinj, ?_⟩
  intro X
  obtain ⟨k, V, hV, ⟨e⟩⟩ := finiteSimpleSum_biproduct
    (center_finite_simple_sum_of_loop_centrality C p hp hslide hne X)
  obtain ⟨m, ⟨r⟩⟩ := regroup_biproduct S V (fun j => hcover (V j) (hV j))
  exact ⟨m, ⟨e ≪≫ r⟩⟩

/-- Under centre rigidity, the same explicit assumptions construct its full
ground fusion instance. -/
theorem fusion_of_adjunction_and_loop (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I) :
    IsFusionCategory (CategoryTheory.Center C.Obj) :=
  CentreBundle.fusionOfFiniteSemisimple C
    (finite_semisimple_of_adjunction_and_loop C p hp hslide hne I adj)

/-- The same conditional construction gives the global FP-square formula
when the right adjoint has the prescribed underlying induction objects. -/
theorem globalFPDimension_square_of_assembled_fusion (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I)
    (hI : ∀ i, Nonempty ((I.obj (simples C i)).1 ≅ underlying C (simples C i))) :
    letI : IsFusionCategory (CategoryTheory.Center C.Obj) :=
      fusion_of_adjunction_and_loop C p hp hslide hne I adj
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 := by
  letI : IsFusionCategory (CategoryTheory.Center C.Obj) :=
    fusion_of_adjunction_and_loop C p hp hslide hne I adj
  exact globalFPDimension_square_of_adjunction C I adj hI

end PropertyF.Ground.CentreInduction
