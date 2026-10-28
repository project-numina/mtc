module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualBraiding
public import PropertyF.Ground.Dimensions.PivotalPseudoUnitary

/-! The pivotal structure of the base lifts to the rigid centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

/-- Every transported base pivotal component is a morphism in the actual centre. -/
theorem pivotalComponentsCentral_proved (p : Dimensions.PivotalStructure (C := C.Obj)) :
    PivotalComponentsCentral C p := by
  intro Z T
  let F := CategoryTheory.Center.ofBraided C.Obj
  let B := F.obj T
  let u (W : CategoryTheory.Center C.Obj) : W.1 ⟶ ((Wᘁ)ᘁ).1 :=
    (p.iso W.1).hom ≫ (forgetDoubleDualIso C W).inv
  have hu (X Y : CategoryTheory.Center C.Obj) :
      u (X ⊗ Y) = (u X ⊗ₘ u Y) ≫ (Dimensions.doubleDualTensorIso X Y).hom.f := by
    convert (transported_pivotal_tensor C p X Y).symm using 1 <;> rfl
  let b := (β_ Z B).hom
  have hn : b.f ≫ u (B ⊗ Z) = u (Z ⊗ B) ≫ ((bᘁ)ᘁ).f :=
    by simpa [u, Category.assoc] using transported_pivotal_natural C p b
  rw [hu, hu] at hn
  have hb := congrArg CategoryTheory.Center.Hom.f (Dimensions.doubleDualTensorIso_braiding Z B)
  simp only [CategoryTheory.Center.comp_f] at hb
  change (Dimensions.doubleDualTensorIso Z B).hom.f ≫ ((bᘁ)ᘁ).f =
    (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f ≫ (Dimensions.doubleDualTensorIso B Z).hom.f at hb
  simp only [Category.assoc] at hn
  rw [hb] at hn
  have hc : b.f ≫ (u B ⊗ₘ u Z) =
      (u Z ⊗ₘ u B) ≫ (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f := by
    let : IsIso (Dimensions.doubleDualTensorIso B Z).hom.f := by
      change IsIso ((CategoryTheory.Center.forget C.Obj).map (Dimensions.doubleDualTensorIso B Z).hom)
      infer_instance
    apply (cancel_mono (Dimensions.doubleDualTensorIso B Z).hom.f).1
    simpa [Category.assoc] using hn
  let j := (positivePivotalComponent C p T).hom
  have hj : j.f = u B := by
    change _ = (p.iso T).hom ≫ (forgetDoubleDualIso C B).inv
    exact positivePivotalComponent_forget C p T
  let : IsIso (u B) := by
    rw [← hj]
    change IsIso ((CategoryTheory.Center.forget C.Obj).map j)
    infer_instance
  have hbeta := ((Zᘁ)ᘁ).2.naturality (u B)
  change (u Z ▷ T) ≫ (((Zᘁ)ᘁ).2.β T).hom =
    (Z.2.β T).hom ≫ (T ◁ u Z)
  apply (cancel_mono ((u B) ▷ ((Zᘁ)ᘁ).1)).1
  rw [tensorHom_def' (u B) (u Z), tensorHom_def (u Z) (u B)] at hc
  change (Z.2.β T).hom ≫ ((T ◁ u Z) ≫ u B ▷ ((Zᘁ)ᘁ).1) =
    ((u Z ▷ T) ≫ ((Zᘁ)ᘁ).1 ◁ u B) ≫
      (((Zᘁ)ᘁ).2.β ((Bᘁ)ᘁ).1).hom at hc
  change ((Zᘁ)ᘁ).1 ◁ u B ≫ (((Zᘁ)ᘁ).2.β ((Bᘁ)ᘁ).1).hom =
    (((Zᘁ)ᘁ).2.β T).hom ≫ u B ▷ ((Zᘁ)ᘁ).1 at hbeta
  simp only [Category.assoc, hbeta] at hc ⊢
  exact hc.symm
end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

/-- The actual rigid centre has a pivotal structure lifting any base pivotal structure. -/
def canonicalCenterPivotal (p : Dimensions.PivotalStructure (C := C.Obj)) :
    Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj) :=
  liftedPivotalStructure C p (pivotalComponentsCentral_proved C p)

/-- A base pivotal structure with FP dimensions yields centre fusion, a
positive spherical centre, pseudo-unitarity and the categorical dimension square. -/
theorem center_structure_of_fp_pivotal
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ)) :
    ∃ hFusion : IsFusionCategory (CategoryTheory.Center C.Obj),
      letI := hFusion
      let pZ := canonicalCenterPivotal C p
      pZ.IsSpherical ∧
      (∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
        (simples (Integrate.bundledCenter C) i) =
          (fpSimple (Integrate.bundledCenter C) i : ℂ)) ∧
      PseudoUnitary (Integrate.bundledCenter C) ∧
      globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 :=
  center_structure_of_pivotal_centrality C p hsimple (pivotalComponentsCentral_proved C p)

end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
/-- If a pseudo-unitary base category admits a pivotal structure, its actual
rigid centre is fusion, positive spherical and pseudo-unitary with the expected
global dimension. Pivotal existence and centre rigidity remain hypotheses. -/
theorem center_structure_of_pivotal_pseudoUnitary
    (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary C) :
    ∃ hFusion : IsFusionCategory (CategoryTheory.Center C.Obj),
      letI := hFusion
      ∃ pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj),
        pZ.IsSpherical ∧
        (∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
          (simples (Integrate.bundledCenter C) i) =
            (fpSimple (Integrate.bundledCenter C) i : ℂ)) ∧
        PseudoUnitary (Integrate.bundledCenter C) ∧
        globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 := by
  obtain ⟨q, _, hq⟩ := Dimensions.positive_spherical_of_pivotal_pseudoUnitary C p hpu
  obtain ⟨hFusion, h⟩ := center_structure_of_fp_pivotal C q hq
  exact ⟨hFusion, canonicalCenterPivotal C q, h⟩
end PropertyF.Ground.CentreInduction
