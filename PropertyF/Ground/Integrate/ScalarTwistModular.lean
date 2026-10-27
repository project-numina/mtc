module
public import PropertyF.Ground.Integrate.ScalarTwistTransport
public import PropertyF.Ground.Fusion.FunctorDimension
public import PropertyF.Ground.Modular.SMatrix

/-! FP dimensions, pivotal traces, and categorical S matrices under scalar twist. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.ScalarTwist
universe v u
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- FP dimension is unchanged on every object. -/
theorem fpDimension_twist (X : C.Obj) :
    fpDimension (category C σ) X = fpDimension C X := by
  let E := conjugate C σ
  let F := E.equivalence.functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  letI : F.Faithful := inferInstanceAs E.equivalence.functor.Faithful
  letI : F.Monoidal := E.monoidal
  exact fpDimension_functor C (category C σ) F X

/-- A pivotal trace scalar is carried through σ. -/
theorem rightTrace_twist (p : Dimensions.PivotalStructure (C := C.Obj))
    {X : C.Obj} (f : X ⟶ X) :
    Dimensions.groundUnitScalarEquiv (category C σ) ((pivotal C σ p).rightTrace f) =
      σ (Dimensions.groundUnitScalarEquiv C (p.rightTrace f)) := by
  simp only [Dimensions.groundUnitScalarEquiv_apply]
  exact unitScalar_twist C σ _

/-- A double-braiding trace is carried through σ. -/
theorem SEntry_twist (p : Dimensions.PivotalStructure (C := C.Obj))
    (X Y : C.Obj) :
    unitScalarEquiv (category C σ) (Modular.SEntry (pivotal C σ p) X Y) =
      σ (unitScalarEquiv C (Modular.SEntry p X Y)) := by
  simp only [← unitScalar_eq_equiv]
  exact unitScalar_twist C σ _

/-- One bijection transports simple FP dimensions, pivotal dimensions and all S entries. -/
theorem labels_S (p : Dimensions.PivotalStructure (C := C.Obj)) :
    ∃ e : Fin (rank C) ≃ Fin (rank (category C σ)),
      (∀ i, fpSimple C i = fpSimple (category C σ) (e i)) ∧
      (∀ i, Dimensions.pivotalDimension (category C σ) (pivotal C σ p)
          (simples (category C σ) (e i)) =
        σ (Dimensions.pivotalDimension C p (simples C i))) ∧
      (∀ i j, Modular.categoricalS (category C σ) (pivotal C σ p) (e i) (e j) =
        σ (Modular.categoricalS C p i j)) := by
  obtain ⟨e, he⟩ := Modular.simpleLabels_equiv C (category C σ) (conjugate C σ).equivalence
  refine ⟨e, Modular.conjugate_fpSimple C (category C σ) (conjugate C σ) e he, ?_, ?_⟩
  · intro i
    rw [← pivotalDimension_twist C σ p (simples C i)]
    exact (Dimensions.pivotalDimension_iso (category C σ) (pivotal C σ p) (he i).some).symm
  · intro i j
    unfold Modular.categoricalS
    rw [← SEntry_twist C σ p (simples C i) (simples C j)]
    congr 1
    rw [← Modular.SEntry_iso_right (pivotal C σ p) _ (he j).some]
    rw [Modular.SEntry_symmetric, ← Modular.SEntry_iso_right (pivotal C σ p) _ (he i).some,
      Modular.SEntry_symmetric]
    rfl

end PropertyF.Ground.ScalarTwist
