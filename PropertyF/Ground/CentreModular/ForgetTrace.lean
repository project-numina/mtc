module
public import PropertyF.Ground.CentreModular.CompatiblePivotal
public import PropertyF.Ground.CentreModular.InducedKirby

/-! Comparing arbitrary centre traces with underlying pivotal traces. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- The forgetful functor preserves the pivotal trace of an arbitrary
endomorphism when the pivotal component is compatible with its dual comparison. -/
theorem forget_pivotalTrace
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (Z : CategoryTheory.Center C.Obj) (f : Z ⟶ Z)
    (hcompat : ((pZ.iso Z).hom.f) ≫ (CentreInduction.forgetDoubleDualIso C Z).hom =
      (p.iso Z.1).hom) :
    (pZ.rightTrace f).asHom.f = (p.rightTrace f.f).asHom := by
  let e := CentreInduction.forgetDualIso C Z
  let e' := CentreInduction.forgetDualIso C (Zᘁ)
  let u : Z.1 ⟶ ((Zᘁ)ᘁ).1 := f.f ≫ (pZ.iso Z).hom.f
  have hu : u ≫ e'.hom ≫ (e.invᘁ) = f.f ≫ (p.iso Z.1).hom := by
    simpa [CentreInduction.forgetDoubleDualIso, Dimensions.rightDualIsoMap, e, e', u,
      Category.assoc] using congrArg (fun a => f.f ≫ a) hcompat
  have htrans : u ≫ e'.hom = (f.f ≫ (p.iso Z.1).hom) ≫ (e.homᘁ) := by
    rw [← hu]
    simp only [Category.assoc, ← comp_rightAdjointMate, Iso.hom_inv_id,
      rightAdjointMate_id, Category.comp_id]
  have heval := Dimensions.rightDualIso_evaluation (CentreInduction.forgetPairing C (Zᘁ)) HasRightDual.exact
  change (e'.hom ▷ ((Zᘁ).1)) ≫ ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) = (ε_ (Zᘁ) ((Zᘁ)ᘁ)).f at heval
  have ht := Dimensions.trace_change_rightDual (CentreInduction.forgetPairing C Z) HasRightDual.exact
    (f.f ≫ (p.iso Z.1).hom)
  change (η_ Z (Zᘁ)).f ≫ (((f.f ≫ (p.iso Z.1).hom) ≫ (e.homᘁ)) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
      ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) =
    η_ Z.1 (Z.1ᘁ) ≫ ((f.f ≫ (p.iso Z.1).hom) ⊗ₘ 𝟙 (Z.1ᘁ)) ≫ ε_ (Z.1ᘁ) ((Z.1ᘁ)ᘁ) at ht
  have hn : (pZ.rightTrace f).asHom.f =
      (η_ Z (Zᘁ)).f ≫ ((u ≫ e'.hom) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
        ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) := by
    dsimp [Dimensions.PivotalStructure.rightTrace]
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id,
      CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerRight_f]
    rw [← heval]
    simp [comp_whiskerRight, Category.assoc, u]
  rw [hn, htrans, ht]
  simp [Dimensions.PivotalStructure.rightTrace]

/-- With compatible pivotal components, a centre Hopf link is the base
pivotal trace of the two actual half-braidings. -/
theorem center_SEntry_eq_underlying_trace
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (X Y : CategoryTheory.Center C.Obj)
    (hcompat : ((pZ.iso (X ⊗ Y)).hom.f) ≫
      (CentreInduction.forgetDoubleDualIso C (X ⊗ Y)).hom = (p.iso (X.1 ⊗ Y.1)).hom) :
    unitScalarEquiv (Integrate.bundledCenter C) (Modular.SEntry pZ X Y) =
      unitScalar C (p.rightTrace ((X.2.β Y.1).hom ≫ (Y.2.β X.1).hom)) := by
  rw [← unitScalar_eq_equiv, ← center_forget_unitScalar C]
  congr 1
  apply End.ext
  have h := forget_pivotalTrace C p pZ (X ⊗ Y) (Modular.doubleBraiding X Y) hcompat
  change (pZ.rightTrace (Modular.doubleBraiding X Y)).asHom.f =
    (p.rightTrace ((X.2.β Y.1).hom ≫ (Y.2.β X.1).hom)).asHom at h
  exact h

/-- The centre Kirby sum is an explicit base-category weighted trace of the
induction crossing and the tested centre half-braiding. -/
theorem center_kirby_sum_eq_base_traces
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (k : Fin (rank (Integrate.bundledCenter C)))
    (hcompat : ∀ i, let X := (CentreInduction.induction C).obj (simples C i)
      let Y := simples (Integrate.bundledCenter C) k
      ((pZ.iso (X ⊗ Y)).hom.f) ≫ (CentreInduction.forgetDoubleDualIso C (X ⊗ Y)).hom =
        (p.iso (X.1 ⊗ Y.1)).hom) :
    (∑ j, (fpSimple (Integrate.bundledCenter C) j : ℂ) *
      Modular.categoricalS (Integrate.bundledCenter C) pZ j k) =
    ∑ i, (fpSimple C i : ℂ) * unitScalar C (p.rightTrace
      (CentreInduction.crossingCandidate C (simples C i)
        (simples (Integrate.bundledCenter C) k).1 ≫
      (((simples (Integrate.bundledCenter C) k).2.β
        (CentreInduction.underlying C (simples C i))).hom))) := by
  rw [center_kirby_sum_eq_induced C pZ k]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact center_SEntry_eq_underlying_trace C p pZ _ _ (hcompat i)

end PropertyF.Ground.CentreModular
