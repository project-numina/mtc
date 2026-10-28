module
public import PropertyF.Ground.CentreModular.VafaCompletion
public import PropertyF.Ground.CentreCabling.TwistFinite

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- Pivotal twist scalars have finite order whenever its actual balancing law
holds; no lantern relation or modularity hypothesis is used. -/
theorem pivotal_twist_finite_of_balancing
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom) :
    ∀ i, IsOfFinOrder (End.of ((Dimensions.pivotalBraidedTwist C p (simples C i)).hom)) := by
  let η := Dimensions.pivotalBraidedTwistNaturalIso C p
  let t := CentreCabling.pivotalTwistUnit C p
  have ht (i : Fin (rank C)) : (η.app (simples C i)).hom = (t i : ℂ) • 𝟙 (simples C i) := by
    let : Simple (simples C i) := simples_simple C i
    exact Dimensions.pivotalBraidedTwist_simple C p (simples C i)
  have hb (i j : Fin (rank C)) : η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j) := by
    apply Iso.ext
    have h := hbalance (simples C i) (simples C j)
    change Modular.doubleBraiding _ _ ≫ ((η.app (simples C i)).hom ⊗ₘ
      (η.app (simples C j)).hom) = (η.app (simples C i ⊗ simples C j)).hom at h
    rw [ht i, ht j] at h
    simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul,
      MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, Linear.comp_smul, smul_smul] at h
    simpa [scalarIso, monodromyIso, Modular.doubleBraiding, Category.assoc,
      Linear.smul_comp, mul_comm] using h.symm
  have hf := natural_scalars_finite_of_simple_balancing C η t ht hb
  intro i
  have hf' : IsOfFinOrder ((t i : ℂˣ) : ℂ) := Units.isOfFinOrder_val.mpr (hf i)
  let : Simple (simples C i) := simples_simple C i
  have hm := (Dimensions.simpleEndScalarEquiv C (simples C i)).symm.toMonoidHom.isOfFinOrder hf'
  simpa [t, CentreCabling.pivotalTwistUnit, Dimensions.pivotalBraidedTwistScalar] using hm

/-- The actual pivotal twist balancing law alone forces every mixed
monodromy to have finite order; no lantern relation is required. -/
theorem mixed_monodromy_finite_of_pivotal_balancing
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom)
    (X Y : C.Obj) : IsOfFinOrder (End.of (Modular.doubleBraiding X Y)) := by
  apply CentreCabling.mixed_monodromy_finite_of_balanced_finite_twist C
    (Dimensions.pivotalBraidedTwistNaturalIso C p)
  · exact pivotal_twist_finite_of_balancing C p hbalance
  · exact hbalance

end PropertyF.Ground.CentreModular
